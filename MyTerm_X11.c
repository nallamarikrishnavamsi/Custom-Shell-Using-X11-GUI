#define _POSIX_C_SOURCE 200809L
#define _GNU_SOURCE
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <strings.h>
#include <fcntl.h>
#include <dirent.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <errno.h>
#include <time.h>
#include <signal.h>
#include <glob.h>
#include <limits.h>
#include <wordexp.h>
#include <sys/select.h>
#include <sys/time.h>
#include <X11/Xlib.h>
#include <X11/keysym.h>
#include <pwd.h>
#include <stdint.h>
#include <wchar.h>
#include <X11/Xutil.h>

#define WIDTH 900
#define HEIGHT 600
#define MAX_TABS 100
#define MAX_LINES 1000
#define MAX_LINE_LEN 4096

#define LEFT_MARGIN 6
#define TOP_MARGIN 20
#define SCROLL_STEP 3
#define HISTORY_MAX 10000
#define HISTORY_SHOW 1000
#define BUF_SIZE 1024
#define MAX_CMDS 16

typedef struct {
    char *cmd;
    int fd[2];
    pid_t pid;
    long offset;
} MWCommand;

typedef struct {
    pid_t pid;
    int to_child[2];
    int from_child[2];
    char *lines[MAX_LINES];
    int  is_command[MAX_LINES];
    int  lines_count;
    char current_line[MAX_LINE_LEN];
    int  current_len;
    int  cursor_pos;
    char cwd[PATH_MAX];
    int scroll_offset;
    char stream_line[MAX_LINE_LEN];
    int  stream_len;
    MWCommand mw_cmds[MAX_CMDS];
    int mw_n;
    int mw_maxfd;

    char *autocomplete_matches[1024];
    int  autocomplete_count;
    int  autocomplete_start;
    int  autocomplete_pos;
} Tab;

static char *history[HISTORY_MAX];
static int history_count = 0;
static int history_start = 0;
static char history_path[PATH_MAX];
int cursor_visible = 1;
static XFontSet fontset = NULL;
static int font_ascent = 13;
static int font_descent = 5;
static int FONT_HEIGHT;

static void make_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags == -1) return;
    fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

void scroll_to_cursor(Tab *t);
static void append_text(Tab *t, const char *s, int n);
static void draw_ui(Display *display, Window win, GC gc, XFontStruct *font, Tab *t,
                    int active, int tab_count, int search_mode, char *search_buf, int search_len, int search_cursor);

static int is_utf8_continuation(unsigned char c) 
{
    return (c & 0xC0) == 0x80;
}
static int utf8_text_width(XFontStruct *fallback_font, const char *text, int len)
{
    if (!text || len <= 0) return 0;
    if (fontset) 
    {
        XRectangle ink, logical;
        Xutf8TextExtents(fontset, text, len, &ink, &logical);
        return logical.width;
    }
    if (fallback_font) 
    {
        return XTextWidth(fallback_font, text, len);
    }
    return 0;
}
static void push_line(Tab *t, const char *line) 
{
    if (t->lines_count >= MAX_LINES) 
    {
        free(t->lines[0]);
        memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
        memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
        t->lines_count--;
    }
    t->lines[t->lines_count] = strdup(line ? line : "");
    t->is_command[t->lines_count] = 0;
    t->lines_count++;
}
static void custom_echo_handler(Tab *t, const char *input)
{
    const char *p = input;
    while (*p && !isspace((unsigned char)*p)) p++;
    while (*p && isspace((unsigned char)*p)) p++;
    if (*p != '"') 
    {
        push_line(t, "Error: echo requires a quoted string.");
        return;
    }
    p++;
    const char *start = p;
    const char *end = strrchr(start, '"');
    if (!end) 
    {
        push_line(t, "Error: unclosed quote in echo command.");
        return;
    }
    int len = (int)(end - start);
    char content[MAX_LINE_LEN];
    strncpy(content, start, len);
    content[len] = '\0';
    char output[MAX_LINE_LEN];
    int out_idx = 0;
    int in_idx = 0;
    while (in_idx < len && out_idx < MAX_LINE_LEN - 1) 
    {
        if (content[in_idx] == '\n' || content[in_idx] == '\r') 
        {
            in_idx++;
            continue;
        }
        if (content[in_idx] == '\\' &&
            in_idx + 2 < len &&
            content[in_idx + 1] == 'n' &&
            content[in_idx + 2] == '\\') {
            if (out_idx > 0 && output[out_idx - 1] == ' ')
                out_idx--;
            output[out_idx++] = '\n';
            in_idx += 3;
            continue;
        }
        output[out_idx++] = content[in_idx++];
    }
    output[out_idx] = '\0';

    char *line_start = output;
    char *p2 = output;
    while (*p2) 
    {
        if (*p2 == '\n') 
        {
            *p2 = '\0';
            char *trim = line_start;
            while (*trim == ' ') trim++;
            char *endp = trim + strlen(trim);
            while (endp > trim && endp[-1] == ' ') *--endp = '\0';
            push_line(t, trim);
            line_start = p2 + 1;
        }
        p2++;
    }

    char *trim = line_start;
    while (*trim == ' ') trim++;
    char *endp = trim + strlen(trim);
    while (endp > trim && endp[-1] == ' ') *--endp = '\0';
    push_line(t, trim);
    scroll_to_cursor(t);
}

static int utf8_char_len(unsigned char first_byte) 
{
    if ((first_byte & 0x80) == 0) return 1;
    if ((first_byte & 0xE0) == 0xC0) return 2;
    if ((first_byte & 0xF0) == 0xE0) return 3;
    if ((first_byte & 0xF8) == 0xF0) return 4;
    return 1;
}
static void push_command_line(Tab *t, const char *line) 
{
    if (t->lines_count >= MAX_LINES) 
    {
        free(t->lines[0]);
        memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
        memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
        t->lines_count--;
    }
    t->lines[t->lines_count] = strdup(line ? line : "");
    t->is_command[t->lines_count] = 1;
    t->lines_count++;
}

static const char *get_last_user_command(Tab *t) 
{
    if (!t) return NULL;
    for (int i = t->lines_count - 1; i >= 0; --i) {
        if (t->is_command[i] == 1 && t->lines[i] && t->lines[i][0] != '\0')
            return t->lines[i];
    }
    return NULL;
}

static void debug_print_argv(char *argv[], int argc) 
{
    fprintf(stderr, "DEBUG: argc=%d\n", argc);
    for (int i = 0; i < argc; ++i) {
        if (!argv[i]) { fprintf(stderr, "DEBUG: argv[%d]=NULL\n", i); continue; }
        fprintf(stderr, "DEBUG: argv[%d]=\"", i);
        for (size_t j = 0; j < strlen(argv[i]); ++j) {
            unsigned char c = (unsigned char)argv[i][j];
            if (c >= 32 && c < 127) fputc(c, stderr);
            else if (c == '\n') fputs("\\n", stderr);
            else if (c == '\t') fputs("\\t", stderr);
            else fprintf(stderr, "\\x%02X", c);
        }
        fputs("\"\n", stderr);
    }
}
static void handle_echo(Tab *t, char *argv[], int argc) 
{
    if (argc <= 1) 
    {
        push_line(t, "");
        scroll_to_cursor(t);
        return;
    }
    size_t total = 0;
    for (int i = 1; i < argc; i++) total += strlen(argv[i]) + 1;
    char *full = malloc(total + 1);
    if (!full) return;
    full[0] = '\0';
    for (int i = 1; i < argc; i++) 
    {
        if (i > 1) strcat(full, " ");
        strcat(full, argv[i]);
    }
    char *line_start = full;
    char *p = full;
    while (*p) 
    {
        if (*p == '\n') 
        {
            *p = '\0';
            push_line(t, line_start);
            line_start = p + 1;
        }
        p++;
    }
    if (*line_start) push_line(t, line_start);
    free(full);
    scroll_to_cursor(t);
}
static int parse_command_line(const char *line, char *argv[], int max_args, char **allocated_buf) 
{
    if (!line || !argv || max_args <= 0) return 0;
    size_t len = strlen(line);
    char *buf = malloc(len + 1);
    if (!buf) return 0;
    *allocated_buf = buf;
    int argc = 0;
    const char *p = line;
    while (*p && argc < max_args - 1) 
    {
        while (*p == ' ' || *p == '\t') p++;
        if (!*p) break;
        argv[argc++] = buf;
        if (*p == '"' || *p == '\'') 
        {
            char quote = *p++;
            while (*p && *p != quote) {
                if (*p == '\\' && *(p+1)) 
                {
                    p++;
                    switch (*p) 
                    {
                        case 'n': *buf++ = '\n'; break;
                        case 't': *buf++ = '\t'; break;
                        case 'r': *buf++ = '\r'; break;
                        case '\\': *buf++ = '\\'; break;
                        case '"': *buf++ = '"'; break;
                        case '\'': *buf++ = '\''; break;
                        default: *buf++ = *p; break;
                    }
                    p++;
                } 
                else 
                {
                    *buf++ = *p++;
                }
            }
            if (*p == quote) p++;
        } 
        else 
        {
            while (*p && *p != ' ' && *p != '\t') 
            {
                if (*p == '\\' && *(p+1)) 
                {
                    p++;
                    *buf++ = *p++;
                } 
                else 
                {
                    *buf++ = *p++;
                }
            }
        }
        *buf++ = '\0';
    }
    argv[argc] = NULL;
    return argc;
}

void scroll_to_cursor(Tab *t) 
{
    int max_visible = (HEIGHT - TOP_MARGIN - FONT_HEIGHT) / FONT_HEIGHT;
    if (max_visible < 1) max_visible = 1;
    if (t->lines_count > max_visible) 
    {
        t->scroll_offset = t->lines_count - max_visible;
    } 
    else 
    {
        t->scroll_offset = 0;
    }
}
void scroll_up(Tab *t) 
{
    if (t->scroll_offset > 0)
        t->scroll_offset -= SCROLL_STEP;
    if (t->scroll_offset < 0) t->scroll_offset = 0;
}
void scroll_down(Tab *t) 
{
    int max_visible = (HEIGHT - TOP_MARGIN - FONT_HEIGHT) / FONT_HEIGHT;
    if (max_visible < 1) max_visible = 1;
    int max_offset = (t->lines_count > max_visible) ? (t->lines_count - max_visible) : 0;
    if (t->scroll_offset < max_offset)
        t->scroll_offset += SCROLL_STEP;
    if (t->scroll_offset > max_offset) t->scroll_offset = max_offset;
}

static void load_history_file(void) 
{
    struct passwd *pw = getpwuid(getuid());
    const char *home = pw ? pw->pw_dir : getenv("HOME");
    if (!home) return;
    snprintf(history_path, sizeof(history_path), "%s/.myterm_history", home);
    FILE *f = fopen(history_path, "r");
    if (!f) return;
    char line[4096];
    while (fgets(line, sizeof(line), f)) 
    {
        size_t L = strlen(line);
        if (L && line[L-1] == '\n') line[L-1] = '\0';
        if (history_count < HISTORY_MAX) {
            history[history_count++] = strdup(line);
        } 
        else 
        {
            free(history[history_start]);
            history[history_start] = strdup(line);
            history_start = (history_start + 1) % HISTORY_MAX;
        }
    }
    fclose(f);
}
static void append_history_file(const char *cmd) 
{
    if (history_path[0] == '\0' || !cmd || cmd[0]=='\0') return;
    FILE *f = fopen(history_path, "a");
    if (!f) return;
    fprintf(f, "%s\n", cmd);
    fclose(f);
}
static void add_history(const char *cmd) 
{
    if (!cmd || cmd[0]=='\0') return;
    if (history_count < HISTORY_MAX) 
    {
        history[history_count++] = strdup(cmd);
    }
    else 
    {
        free(history[history_start]);
        history[history_start] = strdup(cmd);
        history_start = (history_start + 1) % HISTORY_MAX;
    }
    append_history_file(cmd);
}
static void show_history_in_tab(Tab *t) 
{
    if (history_count == 0) 
    {
        if (t->lines_count >= MAX_LINES) 
        {
            free(t->lines[0]);
            memmove(&t->lines[0], &t->lines[1], sizeof(char*)*(MAX_LINES-1));
            memmove(&t->is_command[0], &t->is_command[1], sizeof(int)*(MAX_LINES-1));
            t->lines_count--;
        }
        t->lines[t->lines_count] = strdup("(no history)");
        t->is_command[t->lines_count++] = 0;
        scroll_to_cursor(t);
        return;
    }
    int shown = 0;
    for (int i = history_count - 1; i >= 0 && shown < HISTORY_SHOW; --i, ++shown) 
    {
        int idx = i % HISTORY_MAX;
        if (!history[idx]) continue;
        if (t->lines_count >= MAX_LINES) 
        {
            free(t->lines[0]);
            memmove(&t->lines[0], &t->lines[1], sizeof(char*)*(MAX_LINES-1));
            memmove(&t->is_command[0], &t->is_command[1], sizeof(int)*(MAX_LINES-1));
            t->lines_count--;
        }
        t->lines[t->lines_count] = strdup(history[idx]);
        t->is_command[t->lines_count++] = 0;
    }
    scroll_to_cursor(t);
}

static int longest_common_substring_len(const char *a, const char *b) 
{
    int la = (int)strlen(a), lb = (int)strlen(b);
    if (la == 0 || lb == 0) return 0;
    int *prev = calloc(lb+1, sizeof(int));
    int *cur = calloc(lb+1, sizeof(int));
    int best = 0;
    for (int i = 1; i <= la; ++i) 
    {
        for (int j = 1; j <= lb; ++j) 
        {
            if (a[i-1] == b[j-1]) 
            {
                cur[j] = prev[j-1] + 1;
                if (cur[j] > best) best = cur[j];
            } else cur[j] = 0;
        }
        int *tmp = prev; prev = cur; cur = tmp;
        memset(cur, 0, (lb+1)*sizeof(int));
    }
    free(prev); free(cur);
    return best;
}
static void perform_history_search_and_print(Tab *t, const char *term) 
{
    if (!term || term[0] == '\0') 
    {
        if (t->lines_count >= MAX_LINES) 
        {
            free(t->lines[0]);
            memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
            memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
            t->lines_count--;
        }
        t->lines[t->lines_count] = strdup("Empty search term");
        t->is_command[t->lines_count++] = 0;
        scroll_to_cursor(t);
        return;
    }
    for (int i = history_count - 1; i >= 0; --i) 
    {
        int idx = i % HISTORY_MAX;
        if (history[idx] && strcmp(history[idx], term) == 0) 
        {
            if (t->lines_count >= MAX_LINES) 
            {
                free(t->lines[0]);
                memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                t->lines_count--;
            }
            t->lines[t->lines_count] = strdup(history[idx]);
            t->is_command[t->lines_count++] = 0;
            scroll_to_cursor(t);
            return;
        }
    }
    int best_len = 0;
    for (int i = 0; i < history_count; ++i) 
    {
        int idx = i % HISTORY_MAX;
        if (!history[idx]) continue;
        int lcs = longest_common_substring_len(term, history[idx]);
        if (lcs > best_len) best_len = lcs;
    }

    if (best_len <= 2) 
    {
        if (t->lines_count >= MAX_LINES) 
        {
            free(t->lines[0]);
            memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
            memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
            t->lines_count--;
        }
        t->lines[t->lines_count] = strdup("No match for search term in history");
        t->is_command[t->lines_count++] = 0;
        scroll_to_cursor(t);
        return;
    }
    for (int i = history_count - 1; i >= 0; --i) 
    {
        int idx = i % HISTORY_MAX;
        if (!history[idx]) continue;
        int lcs = longest_common_substring_len(term, history[idx]);
        if (lcs == best_len) {
            if (t->lines_count >= MAX_LINES) 
            {
                free(t->lines[0]);
                memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                t->lines_count--;
            }
            t->lines[t->lines_count] = strdup(history[idx]);
            t->is_command[t->lines_count++] = 0;
        }
    }
    scroll_to_cursor(t);
}

static char *common_prefix_array(char **arr, int n) 
{
    if (n <= 0) return strdup("");
    char *prefix = strdup(arr[0]);
    for (int i = 1; i < n; ++i) 
    {
        int j = 0;
        while (prefix[j] && arr[i][j] && prefix[j] == arr[i][j]) j++;
        prefix[j] = '\0';
    }
    return prefix;
}

static void autocomplete_fill_gui(Tab *t, Display *display, Window win, GC gc, XFontStruct *font) 
{
    int pos = t->cursor_pos;
    if (pos > t->current_len) pos = t->current_len;
    int start = pos - 1;
    while (start >= 0 && !isspace((unsigned char)t->current_line[start])) start--;
    start++;
    int pref_len = pos - start;
    char prefix[MAX_LINE_LEN];
    if (pref_len < 0) pref_len = 0;
    strncpy(prefix, &t->current_line[start], pref_len);
    prefix[pref_len] = '\0';

    for (int i = 0; i < t->autocomplete_count; i++) 
    {
        if (t->autocomplete_matches[i]) 
        {
            free(t->autocomplete_matches[i]);
            t->autocomplete_matches[i] = NULL;
        }
    }
    t->autocomplete_count = 0;

    DIR *d = opendir(t->cwd[0] ? t->cwd : ".");
    if (!d) return;
    struct dirent *ent;
    size_t plen = strlen(prefix);
    while ((ent = readdir(d)) != NULL) 
    {
        if (plen == 0 || strncmp(ent->d_name, prefix, plen) == 0) 
        {
            t->autocomplete_matches[t->autocomplete_count++] = strdup(ent->d_name);
            if (t->autocomplete_count >= 1024) break;
        }
    }
    closedir(d);

    if (t->autocomplete_count == 0) return;

    t->autocomplete_start = start;
    t->autocomplete_pos = pos;

    if (t->autocomplete_count == 1) {
        int matchlen = (int)strlen(t->autocomplete_matches[0]);
        int tail_len = t->current_len - pos;
        if (start + matchlen + tail_len < MAX_LINE_LEN) 
        {
            memmove(&t->current_line[start + matchlen], &t->current_line[pos], tail_len + 1);
            memcpy(&t->current_line[start], t->autocomplete_matches[0], matchlen);
            t->current_len = start + matchlen + tail_len;
            t->cursor_pos = start + matchlen;
        }
        free(t->autocomplete_matches[0]);
        t->autocomplete_matches[0] = NULL;
        t->autocomplete_count = 0;
        scroll_to_cursor(t);
        return;
    }

    char *tmp_arr[1024];
    for (int i = 0; i < t->autocomplete_count; ++i) tmp_arr[i] = t->autocomplete_matches[i];
    char *pref = common_prefix_array(tmp_arr, t->autocomplete_count);
    int pref_len2 = (int)strlen(pref);
    if (pref_len2 > pref_len) 
    {
        int tail_len = t->current_len - pos;
        if (start + pref_len2 + tail_len < MAX_LINE_LEN) 
        {
            memmove(&t->current_line[start + pref_len2], &t->current_line[pos], tail_len + 1);
            memcpy(&t->current_line[start], pref, pref_len2);
            t->current_len = start + pref_len2 + tail_len;
            t->cursor_pos = start + pref_len2;
        }
        free(pref);
        scroll_to_cursor(t);
        return;
    }
    free(pref);

    if (t->lines_count + t->autocomplete_count + 2 >= MAX_LINES) 
    {
        int drop = (t->lines_count + t->autocomplete_count + 2) - MAX_LINES;
        for (int i = 0; i < drop; ++i) 
        {
            free(t->lines[0]);
            memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (t->lines_count - 1));
            memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (t->lines_count - 1));
            t->lines_count--;
        }
    }

    t->lines[t->lines_count] = strdup("Autocomplete options : ");
    t->is_command[t->lines_count++] = 0;

    for (int i = 0; i < t->autocomplete_count && t->lines_count < MAX_LINES; ++i) 
    {
        char tmp[MAX_LINE_LEN + 32];
        snprintf(tmp, sizeof(tmp), "%d. %s", i + 1, t->autocomplete_matches[i]);
        t->lines[t->lines_count] = strdup(tmp);
        t->is_command[t->lines_count++] = 0;
    }
    scroll_to_cursor(t);
    XFlush(display);
}

void autocomplete_select(Tab *t, int key_digit) 
{
    if (key_digit < 1 || key_digit > t->autocomplete_count) return;
    const char *choice = t->autocomplete_matches[key_digit - 1];
    if (!choice) return;

    int start = t->autocomplete_start;
    int pos = t->autocomplete_pos;
    int matchlen = (int)strlen(choice);
    int tail_len = t->current_len - pos;

    if (start + matchlen + tail_len < MAX_LINE_LEN) 
    {
        memmove(&t->current_line[start + matchlen], &t->current_line[pos], tail_len + 1);
        memcpy(&t->current_line[start], choice, matchlen);
        t->current_len = start + matchlen + tail_len;
        t->cursor_pos = start + matchlen;
    }

    for (int i = 0; i < t->autocomplete_count; ++i) 
    {
        free(t->autocomplete_matches[i]);
        t->autocomplete_matches[i] = NULL;
    }
    t->autocomplete_count = 0;
    scroll_to_cursor(t);
}
static void autocomplete_clear(Tab *t) 
{
    for (int i = 0; i < t->autocomplete_count; ++i) 
    {
        if (t->autocomplete_matches[i]) 
        {
            free(t->autocomplete_matches[i]);
            t->autocomplete_matches[i] = NULL;
        }
    }
    t->autocomplete_count = 0;
    t->autocomplete_start = 0;
    t->autocomplete_pos = 0;
}

static int parse_multiwatch_args(char *input, MWCommand cmds[], int maxcmds) 
{
    char *lb=strchr(input,'[');
    char *rb=strchr(input,']');
    if(!lb || !rb || rb<=lb) return 0;
    char *p=lb+1;
    int n=0;
    while(p<rb && n<maxcmds)
    {
        while(p<rb && isspace((unsigned char)*p)) p++;
        if(*p=='"'||*p=='\'')
        {
            char quote=*p++;
            char tmp[1024]; int ti=0;
            while(p<rb && *p!=quote && ti+1< (int)sizeof(tmp)) tmp[ti++]=*p++;
            tmp[ti]='\0';
            if(*p==quote)p++;
            cmds[n].cmd=strdup(tmp); cmds[n].pid=-1; cmds[n].fd[0]=cmds[n].fd[1]=-1;
            n++;
        } 
        else 
        { 
            while(p<rb && *p!=',') p++; if(*p==',') p++; 
        }
        while(p<rb && (*p==',' || isspace((unsigned char)*p))) p++;
    }
    return n;
}

static int start_multiwatch_tab(Tab *tab, MWCommand cmds_in[], int n) 
{
    if (n <= 0) return 0;
    if (tab->mw_n != 0) return -1;

    int maxfd = -1;
    for (int i = 0; i < n; ++i) 
    {
        int pfd[2];
        if (pipe(pfd) < 0) 
        {
            perror("pipe");
            for (int j = 0; j < i; ++j) 
            {
                if (tab->mw_cmds[j].fd[0] >= 0) close(tab->mw_cmds[j].fd[0]);
                if (tab->mw_cmds[j].fd[1] >= 0) close(tab->mw_cmds[j].fd[1]);
            }
            return -1;
        }

        pid_t pid = fork();
        if (pid < 0) 
        {
            perror("fork");
            close(pfd[0]); close(pfd[1]);
            for (int j = 0; j < i; ++j) 
            {
                if (tab->mw_cmds[j].fd[0] >= 0) close(tab->mw_cmds[j].fd[0]);
                if (tab->mw_cmds[j].fd[1] >= 0) close(tab->mw_cmds[j].fd[1]);
            }
            return -1;
        }

        if (pid == 0) 
        {
            close(pfd[0]);
            if (dup2(pfd[1], STDOUT_FILENO) < 0) { perror("dup2 stdout"); _exit(127); }
            if (dup2(pfd[1], STDERR_FILENO) < 0) { perror("dup2 stderr"); _exit(127); }
            close(pfd[1]);

            for (;;) 
            {
                char *cmdline = strdup(cmds_in[i].cmd);
                if (!cmdline) _exit(127);
                char *argv[64];
                int argc = 0;
                char *tok = strtok(cmdline, " \t\n");
                while (tok && argc < 63) 
                {
                    argv[argc++] = tok;
                    tok = strtok(NULL, " \t\n");
                }
                argv[argc] = NULL;

                if (argc > 0) 
                {
                    pid_t cpid = fork();
                    if (cpid == 0) {
                        if (execvp(argv[0], argv) < 0) 
                        {
                            perror("execvp");
                            _exit(127);
                        }
                    } 
                    else if (cpid > 0) 
                    {
                        int status;
                        waitpid(cpid, &status, 0);
                    }
                }
                free(cmdline);
                sleep(2);
            }
            _exit(0);
        } 
        else 
        {
            close(pfd[1]);
            tab->mw_cmds[i].cmd = strdup(cmds_in[i].cmd);
            tab->mw_cmds[i].pid = pid;
            tab->mw_cmds[i].fd[0] = pfd[0];
            tab->mw_cmds[i].fd[1] = -1;
            make_nonblocking(tab->mw_cmds[i].fd[0]);

            char fname[64];
            snprintf(fname, sizeof(fname), ".temp.%d.txt", (int)pid);
            int tf = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0644);
            if (tf >= 0) close(tf);
            int tf2 = open(fname, O_WRONLY | O_CREAT | O_APPEND, 0644);
            if (tf2 >= 0)
                tab->mw_cmds[i].fd[1] = tf2;
            else
                tab->mw_cmds[i].fd[1] = -1;

            if (tab->mw_cmds[i].fd[0] > maxfd) maxfd = tab->mw_cmds[i].fd[0];
        }
    }

    tab->mw_n = n;
    tab->mw_maxfd = maxfd;
    return tab->mw_n;
}

static void stop_multiwatch_tab(Tab *tab) 
{
    if (tab->mw_n == 0) return;
    for (int i = 0; i < tab->mw_n; ++i) 
    {
        if (tab->mw_cmds[i].pid > 0) 
        {
            kill(tab->mw_cmds[i].pid, SIGINT);
        }
    }
    for (int i = 0; i < tab->mw_n; ++i) 
    {
        if (tab->mw_cmds[i].pid > 0) waitpid(tab->mw_cmds[i].pid, NULL, 0);
        if (tab->mw_cmds[i].fd[0] >= 0) close(tab->mw_cmds[i].fd[0]);
        if (tab->mw_cmds[i].fd[1] >= 0) close(tab->mw_cmds[i].fd[1]);
        if (tab->mw_cmds[i].cmd) free(tab->mw_cmds[i].cmd);

        char fname[64];
        snprintf(fname, sizeof(fname), ".temp.%d.txt", (int)tab->mw_cmds[i].pid);
        unlink(fname);

        tab->mw_cmds[i].cmd = NULL;
        tab->mw_cmds[i].fd[0] = -1;
        tab->mw_cmds[i].fd[1] = -1;
        tab->mw_cmds[i].pid = -1;
    }
    tab->mw_n = 0;
    tab->mw_maxfd = -1;
}

static void init_tab(Tab *t, const char *inherit_cwd, int tab_number) 
{
    t->pid = -1;
    t->to_child[0] = t->to_child[1] = -1;
    t->from_child[0] = t->from_child[1] = -1;
    for (int j = 0; j < MAX_LINES; ++j) { t->lines[j] = NULL; t->is_command[j] = 0; }
    t->lines_count = 0;
    t->current_len = 0;
    t->cursor_pos = 0;
    t->current_line[0] = '\0';
    t->stream_len = 0;
    t->stream_line[0] = '\0';
    t->mw_n = 0;
    t->mw_maxfd = -1;
    t->scroll_offset = 0;
    for (int i = 0; i < MAX_CMDS; ++i) 
    { 
        t->mw_cmds[i].cmd = NULL;
        t->mw_cmds[i].fd[0] = t->mw_cmds[i].fd[1] = -1;
         t->mw_cmds[i].pid = -1; 
    }
    for (int i = 0; i < 1024; ++i) t->autocomplete_matches[i] = NULL;
    t->autocomplete_count = 0;
    t->autocomplete_start = t->autocomplete_pos = 0;
    if (inherit_cwd && inherit_cwd[0]) strncpy(t->cwd, inherit_cwd, sizeof(t->cwd)-1);
    else if (getcwd(t->cwd, sizeof(t->cwd)) == NULL) t->cwd[0] = '\0';
    char tab_info[64];
    snprintf(tab_info, sizeof(tab_info), "Tab %d", tab_number);
    t->lines[0] = strdup(tab_info);
    t->is_command[0] = 0;
    t->lines_count = 1;
}

static void destroy_tab(Tab *t) 
{
    if (t->pid > 0) 
    {
        kill(-t->pid, SIGKILL);
        waitpid(t->pid, NULL, 0);
    }
    if (t->from_child[0] >= 0) close(t->from_child[0]);
    if (t->to_child[1] >= 0) close(t->to_child[1]);
    stop_multiwatch_tab(t);
    for (int i = 0; i < t->lines_count; ++i) 
    {
        if (t->lines[i]) free(t->lines[i]);
    }
    t->lines_count = 0;
    autocomplete_clear(t);
}

static void spawn_commands_in_tab(Tab *t, char *argv[], int argc) 
{
    char *input_file = NULL, *output_file = NULL;
    char *commands[32][MAX_LINE_LEN/2+32];
    int ncmds = 0;
    int argi = 0, cmd_argc = 0;

    int inpipe[2] = {-1, -1};
    if (pipe(inpipe) < 0) 
    {
        perror("pipe");
        return;
    }

    while (argi < argc) 
    {
        if (strcmp(argv[argi], "<") == 0 && argi+1 < argc) 
        {
            input_file = argv[++argi];
        } 
        else if (strcmp(argv[argi], ">") == 0 && argi+1 < argc) 
        {
            output_file = argv[++argi];
        } 
        else if (strcmp(argv[argi], "|") == 0) 
        {
            commands[ncmds][cmd_argc] = NULL;
            ncmds++;
            cmd_argc = 0;
        } 
        else 
        {
            if (strchr(argv[argi], '*') || strchr(argv[argi], '?')) 
            {
                glob_t g;
                if (glob(argv[argi], 0, NULL, &g) == 0) 
                {
                    for (size_t gi = 0; gi < g.gl_pathc; gi++)
                        commands[ncmds][cmd_argc++] = strdup(g.gl_pathv[gi]);
                }
                else 
                {
                    commands[ncmds][cmd_argc++] = argv[argi];
                }
                globfree(&g);
            } 
            else 
            {
                commands[ncmds][cmd_argc++] = argv[argi];
            }
        }
        argi++;
    }
    commands[ncmds][cmd_argc] = NULL;
    ncmds++;

    int pipes[32][2];
    for (int i = 0; i < ncmds-1; i++)
        if (pipe(pipes[i]) < 0) 
        {
             perror("pipe"); goto skip_exec; 
        }
    int parent_pipe[2];
    if (pipe(parent_pipe) < 0) 
    { 
        perror("pipe"); goto skip_exec; 
    }
    pid_t pgid = 0;
    for (int i = 0; i < ncmds; i++) 
    {
        pid_t pid = fork();
        if (pid < 0) 
        {
            perror("fork");
            goto skip_exec;
        }
        if (pid == 0) 
        {
            setpgid(0, 0);

            if (i == 0 && input_file) 
            {
                int fdin = open(input_file, O_RDONLY);
                if (fdin < 0) { perror("open input"); _exit(127); }
                dup2(fdin, STDIN_FILENO); close(fdin);
            } 
            else if (i == 0) 
            {
                dup2(inpipe[0], STDIN_FILENO);
            } 
            else if (i > 0) 
            {
                dup2(pipes[i-1][0], STDIN_FILENO);
            }

            if (i == ncmds-1) 
            {
                if (output_file) 
                {
                    int fdout = open(output_file, O_WRONLY|O_CREAT|O_TRUNC, 0644);
                    if (fdout < 0) { perror("open output"); _exit(127); }
                    dup2(fdout, STDOUT_FILENO);
                    dup2(fdout, STDERR_FILENO);
                    close(fdout);
                } 
                else 
                {
                    dup2(parent_pipe[1], STDOUT_FILENO);
                    dup2(parent_pipe[1], STDERR_FILENO);
                }
            } 
            else 
            {
                dup2(pipes[i][1], STDOUT_FILENO);
            }

            for (int j = 0; j < ncmds-1; j++) 
            {
                close(pipes[j][0]);
                close(pipes[j][1]);
            }
            close(parent_pipe[0]);
            close(parent_pipe[1]);
            close(inpipe[1]);
            if (t->cwd[0]) chdir(t->cwd);
            execvp(commands[i][0], commands[i]);
            perror("execvp");
            _exit(127);
        } 
        else 
        {
            if (pgid == 0) pgid = pid;
            setpgid(pid, pgid);
            t->pid = pgid;
        }
    }

    for (int i = 0; i < ncmds-1; i++) 
    {
        close(pipes[i][0]);
        close(pipes[i][1]);
    }

    close(parent_pipe[1]);
    t->from_child[0] = parent_pipe[0];
    make_nonblocking(t->from_child[0]);

    close(inpipe[0]);
    t->to_child[1] = inpipe[1];
    t->to_child[0] = -1;
    make_nonblocking(t->to_child[1]);

skip_exec:
    (void)0;
}


static void append_text(Tab *t, const char *s, int n) 
{
    for (int i = 0; i < n; ++i) 
    {
        unsigned char c = (unsigned char)s[i];
        if (c == '\r') continue;

        if (c == '\n') {
            t->stream_line[t->stream_len] = '\0';

            if (t->lines_count >= MAX_LINES) 
            {
                free(t->lines[0]);
                memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                t->lines_count--;
            }
            t->lines[t->lines_count] = strdup(t->stream_line);
            t->is_command[t->lines_count] = 0;
            t->lines_count++;
            t->stream_len = 0;
            t->stream_line[0] = '\0';

            scroll_to_cursor(t);
        } 
        else 
        {
            if (t->stream_len < MAX_LINE_LEN - 1) 
            {
                t->stream_line[t->stream_len++] = (char)c;
            } 
            else 
            {
                t->stream_line[t->stream_len] = '\0';
                if (t->lines_count >= MAX_LINES) 
                {
                    free(t->lines[0]);
                    memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                    memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                    t->lines_count--;
                }
                t->lines[t->lines_count] = strdup(t->stream_line);
                t->is_command[t->lines_count++] = 0;
                t->stream_len = 0;
                t->stream_line[0] = '\0';
            }
        }
    }
}

static int set_tab_cwd(Tab *t, const char *path) 
{
    if (!path) return -1;
    char candidate[PATH_MAX];
    if (path[0] == '/') 
    {
        strncpy(candidate, path, sizeof(candidate)-1);
        candidate[sizeof(candidate)-1] = '\0';
    } 
    else 
    {
        if (t->cwd[0] == '\0') 
        {
            if (!getcwd(candidate, sizeof(candidate))) return -1;
            strncat(candidate, "/", sizeof(candidate) - strlen(candidate) - 1);
            strncat(candidate, path, sizeof(candidate) - strlen(candidate) - 1);
        } 
        else 
        {
            snprintf(candidate, sizeof(candidate), "%s/%s", t->cwd, path);
        }
    }
    struct stat st;
    if (stat(candidate, &st) == 0 && S_ISDIR(st.st_mode)) 
    {
        char realp[PATH_MAX];
        if (realpath(candidate, realp)) 
        {
            strncpy(t->cwd, realp, sizeof(t->cwd)-1);
            t->cwd[sizeof(t->cwd)-1] = '\0';
        } 
        else 
        {
            strncpy(t->cwd, candidate, sizeof(t->cwd)-1);
            t->cwd[sizeof(t->cwd)-1] = '\0';
        }
        return 0;
    } 
    else 
    {
        return -1;
    }
}

void draw_ui(Display *display, Window win, GC gc, XFontStruct *font, Tab *t,
                    int active, int tab_count, int search_mode, char *search_buf, int search_len, int search_cursor)
{
    XClearWindow(display, win);
    int max_visible_history = (HEIGHT - TOP_MARGIN - FONT_HEIGHT) / FONT_HEIGHT;
    if (max_visible_history < 1) max_visible_history = 1;

    if (t->scroll_offset < 0) t->scroll_offset = 0;
    if (t->scroll_offset > t->lines_count) t->scroll_offset = t->lines_count;

    int start = t->scroll_offset;
    int end = start + max_visible_history;
    if (end > t->lines_count) end = t->lines_count;

    int y = TOP_MARGIN;
    for (int li = start; li < end; ++li) {
         if (t->lines[li]) {
            char linebuf[MAX_LINE_LEN + 64];
            if (t->is_command[li]) {
                snprintf(linebuf, sizeof(linebuf), "user@myterm> %s", t->lines[li]);
            } else {
                snprintf(linebuf, sizeof(linebuf), "%s", t->lines[li]);
            }
            if (fontset) {
                Xutf8DrawString(display, win, fontset, gc, LEFT_MARGIN, y,
                                linebuf, (int)strlen(linebuf));
            } else {
                XDrawString(display, win, gc, LEFT_MARGIN, y,
                            linebuf, (int)strlen(linebuf));
            }
        }
        y += FONT_HEIGHT;
    }

    int input_baseline;
    if (t->lines_count == 0)
        input_baseline = TOP_MARGIN + FONT_HEIGHT * 1;
    else
        input_baseline = y;

    if (input_baseline > HEIGHT - FONT_HEIGHT)
        input_baseline = HEIGHT - FONT_HEIGHT;

    const char *prompt = "user@myterm> ";
    int prompt_width = utf8_text_width(font, prompt, (int)strlen(prompt));
    if (fontset) {
        Xutf8DrawString(display, win, fontset, gc, LEFT_MARGIN, input_baseline,
                        prompt, (int)strlen(prompt));
    } else {
        XDrawString(display, win, gc, LEFT_MARGIN, input_baseline,
                    prompt, (int)strlen(prompt));
    }

    if (search_mode) {
        const char *sp = "Enter search term: ";
        int spw = utf8_text_width(font, sp, (int)strlen(sp));
        if (fontset) {
            Xutf8DrawString(display, win, fontset, gc,
                            LEFT_MARGIN + prompt_width, input_baseline,
                            sp, (int)strlen(sp));
        } else {
            XDrawString(display, win, gc,
                        LEFT_MARGIN + prompt_width, input_baseline,
                        sp, (int)strlen(sp));
        }
        if (search_len > 0) {
            if (fontset) {
                Xutf8DrawString(display, win, fontset, gc,
                                LEFT_MARGIN + prompt_width + spw, input_baseline,
                                search_buf, search_len);
            } else {
                XDrawString(display, win, gc,
                            LEFT_MARGIN + prompt_width + spw, input_baseline,
                            search_buf, search_len);
            }
        }
    } else if (t->current_len > 0) {
        if (fontset) {
            Xutf8DrawString(display, win, fontset, gc,
                            LEFT_MARGIN + prompt_width, input_baseline,
                            t->current_line, t->current_len);
        } else {
            XDrawString(display, win, gc,
                        LEFT_MARGIN + prompt_width, input_baseline,
                        t->current_line, t->current_len);
        }
    }

    char tb[64];
    snprintf(tb, sizeof(tb), "[Tab %d/%d]", active + 1, tab_count);
    int tw = utf8_text_width(font, tb, (int)strlen(tb));
    if (fontset) {
        Xutf8DrawString(display, win, fontset, gc,
                        WIDTH - LEFT_MARGIN - tw, TOP_MARGIN - 6,
                        tb, (int)strlen(tb));
    } else {
        XDrawString(display, win, gc,
                    WIDTH - LEFT_MARGIN - tw, TOP_MARGIN - 6,
                    tb, (int)strlen(tb));
    }

    if (cursor_visible) {
        XSetForeground(display, gc, WhitePixel(display, DefaultScreen(display)));
        int cursor_x;
        if (search_mode) {
            const char *sp = "Enter search term: ";
            int spw = utf8_text_width(font, sp, (int)strlen(sp));
            cursor_x = LEFT_MARGIN + prompt_width + spw +
                       utf8_text_width(font, search_buf, search_cursor);
        } else {
            cursor_x = LEFT_MARGIN + prompt_width +
                       utf8_text_width(font, t->current_line, t->cursor_pos);
        }
        int cursor_h = font_ascent + font_descent;
        int cursor_w = 4;
        int cursor_y = input_baseline - font_ascent;
        XFillRectangle(display, win, gc, cursor_x, cursor_y, cursor_w, cursor_h);
    }

    XFlush(display);
}

int main() {
    setlocale(LC_ALL, "");
    const char *loc = setlocale(LC_CTYPE, NULL);
    if (!loc || !strstr(loc, "UTF-8")) {
        setenv("LANG", "en_US.UTF-8", 1);
        setenv("LC_CTYPE", "en_US.UTF-8", 1);
        setlocale(LC_ALL, "");
    }
    setenv("TZ", "Asia/Kolkata", 1);
    tzset();

    signal(SIGCHLD, SIG_IGN);

    history_path[0] = '\0';
    load_history_file();

    Display *display = XOpenDisplay(NULL);
    if (!display) {
        fprintf(stderr, "Cannot open X display.\n");
        return 1;
    }
    XFontStruct *font = NULL;

    char **missing_list = NULL;
    int missing_count = 0;
    char *default_string = NULL;

    fontset = XCreateFontSet(display,
                             "-*-monospace-*-*-*-*-16-*-*-*-*-*-iso10646-1",
                             &missing_list, &missing_count, &default_string);
    if (fontset) {
        XFontStruct **fs_list = NULL;
        char **fn_list = NULL;
        if (XFontsOfFontSet(fontset, &fs_list, &fn_list) > 0 && fs_list[0]) {
            font_ascent = fs_list[0]->ascent;
            font_descent = fs_list[0]->descent;
        }
    }

    font = XLoadQueryFont(display, "fixed");
    if (!font) {
        fprintf(stderr, "Failed to load fallback font.\n");
        XCloseDisplay(display);
        return 1;
    }
    if (!fontset) {
        font_ascent = font->ascent;
        font_descent = font->descent;
    }

    FONT_HEIGHT = font_ascent + font_descent;
    int screen = DefaultScreen(display);
    Window root = RootWindow(display, screen);
    Window win = XCreateSimpleWindow(display, root, 10, 10, WIDTH, HEIGHT, 1,
                                     WhitePixel(display, screen), BlackPixel(display, screen));
    XMapWindow(display, win);
    GC gc = XCreateGC(display, win, 0, NULL);
    XSetForeground(display, gc, WhitePixel(display, screen));
    XSetBackground(display, gc, BlackPixel(display, screen));
    XSelectInput(display, win, KeyPressMask | ExposureMask | ButtonPressMask);
    XSetFont(display, gc, font->fid);
    if (!font) {
        fprintf(stderr, "Cannot load font 'fixed'\n");
        XCloseDisplay(display);
        return 1;
    }
    XSetFont(display, gc, font->fid);

    XIM xim = XOpenIM(display, NULL, NULL, NULL);
    XIC xic = NULL;
    if (xim) {
        xic = XCreateIC(xim,
                        XNInputStyle, XIMPreeditNothing | XIMStatusNothing,
                        XNClientWindow, win,
                        NULL);
    }

    Tab tabs[MAX_TABS];
    int tab_count = 1;
    if (tab_count > MAX_TABS) tab_count = MAX_TABS;
    int active = 0;
    char basecwd[PATH_MAX];
    if (getcwd(basecwd, sizeof(basecwd)) == NULL) basecwd[0] = '\0';
    for (int i = 0; i < MAX_TABS; ++i) {
        tabs[i].scroll_offset = 0;
        init_tab(&tabs[i], basecwd, i+1);
    }

    #define PID_OFF_MAP_SIZE 8192
    static off_t pid_offsets[PID_OFF_MAP_SIZE];
    memset(pid_offsets, 0, sizeof(pid_offsets));

    struct timespec ts = {0, 50000000};
    static long blink_counter = 0;
    int search_mode = 0;
    char search_buf[MAX_LINE_LEN];
    int search_len = 0;
    int search_cursor = 0;
    XEvent ev;

    while (1) 
    {
        while (XPending(display)) 
        {
            XNextEvent(display, &ev);
            if (ev.type == KeyPress) 
            {
                char buf[256];
                KeySym k = NoSymbol;
                int len = 0;
                Status xst = 0;
                if (xic) {
                    len = Xutf8LookupString(xic, &ev.xkey, buf, (int)sizeof(buf)-1, &k, &xst);
                } else {
                    len = XLookupString(&ev.xkey, buf, sizeof(buf)-1, &k, NULL);
                }
                buf[len] = '\0';

                Tab *t = &tabs[active];
                int ctrl = ev.xkey.state & ControlMask;
                int shift = ev.xkey.state & ShiftMask;

                if (search_mode) {
                    if (len == 1) {
                        unsigned char ch = (unsigned char)buf[0];
                        if (ch == 0x1B) {
                            search_mode = 0;
                            search_len = search_cursor = 0;
                            search_buf[0] = '\0';
                        } else if (ch == 0x7F || k == XK_BackSpace) {
                            if (search_cursor > 0) {
                                memmove(&search_buf[search_cursor-1], &search_buf[search_cursor],
                                        search_len - search_cursor + 1);
                                search_cursor--;
                                search_len--;
                            }
                        } else if (ch == '\r' || ch == '\n' || k == XK_Return) {
                            search_buf[search_len] = '\0';
                            perform_history_search_and_print(t, search_buf);
                            search_mode = 0;
                            search_len = search_cursor = 0;
                            search_buf[0] = '\0';
                        } else if (ch >= 32 && ch < 127) {
                            if (search_len < MAX_LINE_LEN-1) {
                                memmove(&search_buf[search_cursor+1], &search_buf[search_cursor],
                                        search_len - search_cursor + 1);
                                search_buf[search_cursor] = ch;
                                search_len++;
                                search_cursor++;
                            }
                        }
                    }
                    continue;
                }

                if (ctrl && shift && (k == XK_T || k == XK_t)) 
                {
                    if (tab_count < MAX_TABS) 
                    {
                        init_tab(&tabs[tab_count], basecwd, tab_count+1);
                        tab_count++;
                        active = tab_count - 1;
                    }
                    continue;
                }
                if (ctrl && shift && (k == XK_W || k == XK_w)) 
                {
                    if (tab_count > 1) 
                    {
                        destroy_tab(&tabs[active]);
                        for (int i = active; i < tab_count-1; ++i) tabs[i] = tabs[i+1];
                        tab_count--;
                        if (active >= tab_count) active = tab_count-1;
                    } 
                    else 
                    {
                        destroy_tab(&tabs[active]);
                        tab_count = 0;
                        XCloseDisplay(display);
                        exit(0);
                    }
                    continue;
                }
                if (ctrl && !shift && k == XK_Tab) 
                {
                    active = (active + 1) % tab_count;
                    continue;
                }
                if (ctrl && shift && k == XK_Tab) 
                {
                    active = (active - 1 + tab_count) % tab_count;
                    continue;
                }
                if (k == XK_Up) 
                { 
                    scroll_up(&tabs[active]); 
                    continue; 
                }
                if (k == XK_Down) 
                { 
                    scroll_down(&tabs[active]); 
                    continue; 
                }
                if (!search_mode && !ctrl && !shift && k == XK_Tab) {
                    autocomplete_fill_gui(t, display, win, gc, font);
                    draw_ui(display, win, gc, font, t, active, tab_count, search_mode, search_buf, search_len, search_cursor);
                    continue;
                }

                if (t->pid > 0 && t->to_child[1] >= 0 && len > 0) {
                    unsigned char ch = (unsigned char)buf[0];
                    if (!(len == 1 && (ch == 0x03 || ch == 0x1A))) {
                        ssize_t w = write(t->to_child[1], buf, len);
                        (void)w;
                        continue;
                    }
                }
                if (t->autocomplete_count > 0 && len == 1) 
                {
                    unsigned char ch = (unsigned char)buf[0];
                    int knum = -1;
                    if (ch >= '1' && ch <= '9') knum = ch - '1';
                    else if (ch == '0' && t->autocomplete_count >= 10) knum = 9;
                    if (knum >= 0 && knum < t->autocomplete_count) 
                    {
                        int matchlen = (int)strlen(t->autocomplete_matches[knum]);
                        int tail_len = t->current_len - t->autocomplete_pos;
                        if (t->autocomplete_start + matchlen + tail_len < MAX_LINE_LEN) 
                        {
                            memmove(&t->current_line[t->autocomplete_start + matchlen],
                                    &t->current_line[t->autocomplete_pos], tail_len + 1);
                            memcpy(&t->current_line[t->autocomplete_start],
                                   t->autocomplete_matches[knum], matchlen);
                            t->current_len = t->autocomplete_start + matchlen + tail_len;
                            t->cursor_pos = t->autocomplete_start + matchlen;
                        } 
                        else 
                        {
                            t->current_len = t->autocomplete_start + matchlen;
                            t->cursor_pos = t->current_len;
                        }
                        for (int i = 0; i < t->autocomplete_count; i++) 
                        {
                            if (t->autocomplete_matches[i]) 
                            { 
                                free(t->autocomplete_matches[i]); 
                                t->autocomplete_matches[i] = NULL; 
                            }
                        }
                        t->autocomplete_count = 0;
                        scroll_to_cursor(t);
                        draw_ui(display, win, gc, font, t, active, tab_count, search_mode, search_buf, search_len, search_cursor);
                        continue;
                    }
                    scroll_to_cursor(t);
                }

                if (len == 1) 
                {
                    unsigned char ch = (unsigned char)buf[0];
                    if (ch == 0x01) 
                    {
                        t->cursor_pos = 0;
                        continue;
                    } 
                    else if (ch == 0x05) 
                    {
                        t->cursor_pos = t->current_len;
                        continue;
                    } 
                    else if (ch == 0x12) 
                    {
                        search_mode = 1;
                        search_len = search_cursor = 0;
                        search_buf[0] = '\0';
                        continue;
                    } 
                    else if (ch == 0x03) 
                    {
                        if (t->pid > 0) 
                        {
                            pid_t pgid = t->pid;
                            kill(-pgid, SIGINT);
                            if (t->lines_count >= MAX_LINES) 
                            {
                                free(t->lines[0]);
                                memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                                memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                                t->lines_count--;
                            }
                            t->lines[t->lines_count] = strdup("^C");
                            t->is_command[t->lines_count] = 0;
                            t->lines_count++;
                            scroll_to_cursor(t);
                        } 
                        else if (t->mw_n > 0) 
                        {
                            for (int i = 0; i < t->mw_n; ++i) 
                            {
                                if (t->mw_cmds[i].pid > 0) 
                                {
                                    kill(t->mw_cmds[i].pid, SIGTERM);
                                    char fname[64];
                                    snprintf(fname, sizeof(fname), ".temp.%d.txt", (int)t->mw_cmds[i].pid);
                                    unlink(fname);
                                }
                            }
                            stop_multiwatch_tab(t);
                            if (t->lines_count >= MAX_LINES) 
                            {
                                free(t->lines[0]);
                                memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                                memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                                t->lines_count--;
                            }
                            t->lines[t->lines_count] = strdup("^C - MultiWatch stopped");
                            t->is_command[t->lines_count] = 0;
                            t->lines_count++;
                            scroll_to_cursor(t);
                        }
                        continue;
                    } 
                    else if (ch == 0x1A) 
                    {
                        if (t->pid > 0) 
                        {
                            pid_t pgid = t->pid;
                            kill(-pgid, SIGTSTP);
                            if (t->lines_count >= MAX_LINES) 
                            {
                                free(t->lines[0]);
                                memmove(&t->lines[0], &t->lines[1], sizeof(char*) * (MAX_LINES - 1));
                                memmove(&t->is_command[0], &t->is_command[1], sizeof(int) * (MAX_LINES - 1));
                                t->lines_count--;
                            }
                            t->lines[t->lines_count] = strdup("[stopped]");
                            t->is_command[t->lines_count] = 0;
                            t->lines_count++;
                            if (t->from_child[0] >= 0) 
                            {
                                close(t->from_child[0]);
                                t->from_child[0] = -1;
                            }
                            t->pid = -1;
                            scroll_to_cursor(t);
                        }
                        continue;
                    }
                }

                if (k == XK_BackSpace || (len == 1 && buf[0] == 0x7F)) 
                {
                    if (t->cursor_pos > 0) 
                    {
                        int del_bytes = 1;
                        int pos = t->cursor_pos - 1;
                        while (pos > 0 && is_utf8_continuation((unsigned char)t->current_line[pos])) 
                        {
                            pos--;
                            del_bytes++;
                        }
                        memmove(&t->current_line[pos],
                                &t->current_line[t->cursor_pos],
                                t->current_len - t->cursor_pos + 1);
                        t->cursor_pos = pos;
                        t->current_len -= del_bytes;
                    }
                    continue;
                }

                if (k == XK_Return || (len == 1 && (buf[0] == '\r' || buf[0] == '\n'))) 
                {
                    if (t->current_len > 0 && t->current_line[t->current_len - 1] == '\\') 
                    {
                        if (t->current_len < MAX_LINE_LEN - 1) 
                        {
                            t->current_line[t->current_len++] = '\n';
                            t->current_line[t->current_len] = '\0';
                            t->cursor_pos = t->current_len;
                        }
                        continue;
                    }

                    t->current_line[t->current_len] = '\0';

                    char *cmdbuf_check = NULL;
                    char *argv_check[MAX_LINE_LEN/2+1];
                    int argc_check = parse_command_line(t->current_line, argv_check, (int)(sizeof(argv_check)/sizeof(argv_check[0])), &cmdbuf_check);
                    int is_echo = (argc_check > 0 && strcasecmp(argv_check[0], "echo") == 0);

                    char display_line[MAX_LINE_LEN];
                    strncpy(display_line, t->current_line, MAX_LINE_LEN - 1);
                    display_line[MAX_LINE_LEN - 1] = '\0';

                    push_command_line(t, display_line);
                    scroll_to_cursor(t);

                    add_history(t->current_line);

                    char *cmdbuf = NULL;
                    char *argv[MAX_LINE_LEN/2+1];
                    int argc = parse_command_line(t->current_line, argv, (int)(sizeof(argv)/sizeof(argv[0])), &cmdbuf);

                    if (argc > 0) 
                    {
                        if (strcasecmp(argv[0], "echo") == 0) 
                        {
                            custom_echo_handler(t, t->current_line);
                        } 
                        else if (strcasecmp(argv[0], "multiwatch") == 0) 
                        {
                            MWCommand mwtmp[MAX_CMDS];
                            int mn = parse_multiwatch_args(t->current_line, mwtmp, MAX_CMDS);
                            if (mn > 0) {
                                if (t->mw_n == 0) {
                                    if (start_multiwatch_tab(t, mwtmp, mn) <= 0) {
                                        push_line(t, "Failed to start multiWatch");
                                    }
                                    scroll_to_cursor(t);
                                }
                            } else {
                                push_line(t, "Usage: multiWatch [\"cmd1\",\"cmd2\",...]");
                                scroll_to_cursor(t);
                            }
                            for (int i = 0; i < mn; ++i) if (mwtmp[i].cmd) free(mwtmp[i].cmd);
                        } 
                        else if (strcmp(argv[0], "cd") == 0) 
                        {
                            if (argc > 1) 
                            {
                                if (set_tab_cwd(t, argv[1]) == 0) 
                                {
                                    char tab_info[64];
                                    snprintf(tab_info, sizeof(tab_info), "Tab %d", active+1);
                                    free(t->lines[0]);
                                    t->lines[0] = strdup(tab_info);
                                    push_line(t, "Directory changed");
                                    scroll_to_cursor(t);
                                } else 
                                {
                                    char errbuf[256];
                                    snprintf(errbuf, sizeof(errbuf), "cd: %s: %s", argv[1], strerror(errno));
                                    push_line(t, errbuf);
                                    scroll_to_cursor(t);
                                }
                            } 
                            else if (getenv("HOME")) 
                            {
                                if (set_tab_cwd(t, getenv("HOME")) == 0) 
                                {
                                    char tab_info[64];
                                    snprintf(tab_info, sizeof(tab_info), "Tab %d", active+1);
                                    free(t->lines[0]);
                                    t->lines[0] = strdup(tab_info);
                                    scroll_to_cursor(t);
                                }
                            }
                        } 
                        else if (strcmp(argv[0], "clear") == 0) 
                        {
                            char tab_label[64];
                            snprintf(tab_label, sizeof(tab_label), "Tab %d", active + 1);
                            if (t->lines[0] == NULL || strcmp(t->lines[0], tab_label) != 0) {
                                free(t->lines[0]);
                                t->lines[0] = strdup(tab_label);
                            }
                            t->is_command[0] = 0;
                            for (int i = 1; i < t->lines_count; i++) {
                                free(t->lines[i]);
                                t->lines[i] = NULL;
                                t->is_command[i] = 0;
                            }
                            t->lines_count = 1;
                            t->scroll_offset = 0;
                        } 
                        else if (strcmp(argv[0], "exit") == 0) 
                        {
                            if (cmdbuf) free(cmdbuf);
                            if (cmdbuf_check) free(cmdbuf_check);
                            if (xic) XDestroyIC(xic);
                            if (xim) XCloseIM(xim);
                            XFreeFont(display, font);
                            XCloseDisplay(display);
                            return 0;
                        } else if (strcmp(argv[0], "history") == 0) {
                            show_history_in_tab(t);
                        } else {
                            spawn_commands_in_tab(t, argv, argc);
                        }
                    }

                    t->current_len = 0;
                    t->cursor_pos = 0;
                    t->current_line[0] = '\0';

                    if (cmdbuf) free(cmdbuf);
                    if (cmdbuf_check) free(cmdbuf_check);
                    continue;
                }

                if (len > 0) {
                    Tab *t2 = &tabs[active];
                    int bytes_to_insert = len;
                    if (t2->current_len + bytes_to_insert < MAX_LINE_LEN - 1) {
                        memmove(&t2->current_line[t2->cursor_pos + bytes_to_insert],
                                &t2->current_line[t2->cursor_pos],
                                t2->current_len - t2->cursor_pos + 1);
                        memcpy(&t2->current_line[t2->cursor_pos], buf, bytes_to_insert);
                        t2->cursor_pos += bytes_to_insert;
                        t2->current_len += bytes_to_insert;
                        t2->current_line[t2->current_len] = '\0';
                    }
                }
                continue;
            } else if (ev.type == ButtonPress) {
                if (ev.xbutton.button == Button4) {
                    scroll_up(&tabs[active]);
                } else if (ev.xbutton.button == Button5) {
                    scroll_down(&tabs[active]);
                }
            }
        }

        fd_set readfds;
        FD_ZERO(&readfds);
        int maxfd = -1;
        for (int i = 0; i < tab_count; ++i) {
            Tab *tt = &tabs[i];
            if (tt->from_child[0] >= 0) {
                FD_SET(tt->from_child[0], &readfds);
                if (tt->from_child[0] > maxfd) maxfd = tt->from_child[0];
            }
            for (int m = 0; m < tt->mw_n; ++m) {
                if (tt->mw_cmds[m].fd[0] >= 0) {
                    FD_SET(tt->mw_cmds[m].fd[0], &readfds);
                    if (tt->mw_cmds[m].fd[0] > maxfd) maxfd = tt->mw_cmds[m].fd[0];
                }
            }
        }

        struct timeval tv = {0, 10000};
        if (maxfd >= 0) {
            int ready = select(maxfd+1, &readfds, NULL, NULL, &tv);
            if (ready > 0) {
                for (int i = 0; i < tab_count; ++i) {
                    Tab *tt = &tabs[i];
                    if (tt->from_child[0] >= 0 && FD_ISSET(tt->from_child[0], &readfds)) {
                        char rbuf[512];
                        ssize_t rn;
                        while ((rn = read(tt->from_child[0], rbuf, sizeof(rbuf))) > 0) 
                        {
                            append_text(tt, rbuf, (int)rn);
                        }

                        if (rn == 0) 
                        {
                            if (tt->stream_len > 0) {
                                tt->stream_line[tt->stream_len] = '\0';
                                if (tt->lines_count >= MAX_LINES) {
                                    free(tt->lines[0]);
                                    memmove(&tt->lines[0], &tt->lines[1], sizeof(char*) * (MAX_LINES - 1));
                                    memmove(&tt->is_command[0], &tt->is_command[1], sizeof(int) * (MAX_LINES - 1));
                                    tt->lines_count--;
                                }
                                tt->lines[tt->lines_count] = strdup(tt->stream_line);
                                tt->is_command[tt->lines_count++] = 0;
                                tt->stream_len = 0;
                                tt->stream_line[0] = '\0';
                            }
                            close(tt->from_child[0]);
                            tt->from_child[0] = -1;
                            tt->pid = -1;
                        } else if (rn < 0 && errno != EAGAIN && errno != EWOULDBLOCK) {
                            if (tt->stream_len > 0) {
                                tt->stream_line[tt->stream_len] = '\0';
                                if (tt->lines_count >= MAX_LINES) {
                                    free(tt->lines[0]);
                                    memmove(&tt->lines[0], &tt->lines[1], sizeof(char*) * (MAX_LINES - 1));
                                    memmove(&tt->is_command[0], &tt->is_command[1], sizeof(int) * (MAX_LINES - 1));
                                    tt->lines_count--;
                                }
                                tt->lines[tt->lines_count] = strdup(tt->stream_line);
                                tt->is_command[tt->lines_count++] = 0;
                                tt->stream_len = 0;
                                tt->stream_line[0] = '\0';
                            }
                            close(tt->from_child[0]);
                            tt->from_child[0] = -1;
                            tt->pid = -1;
                        }

                        if (i == active) scroll_to_cursor(tt);
                    }
                }

                for (int ti = 0; ti < tab_count; ++ti) {
                    Tab *tt = &tabs[ti];
                    if (tt->mw_n > 0) {
                        for (int m = 0; m < tt->mw_n; ++m) {
                            int fd = tt->mw_cmds[m].fd[0];
                            if (fd >= 0 && FD_ISSET(fd, &readfds)) {
                                char bufm[BUF_SIZE];
                                ssize_t r = read(fd, bufm, sizeof(bufm));
                                if (r > 0) {
                                    char fname[64];
                                    snprintf(fname, sizeof(fname), ".temp.%d.txt", (int)tt->mw_cmds[m].pid);
                                    int tf = open(fname, O_WRONLY | O_CREAT | O_APPEND, 0644);
                                    if (tf >= 0) {
                                        write(tf, bufm, (size_t)r);
                                        close(tf);
                                    }

                                    int pid_for_file = (int)tt->mw_cmds[m].pid;
                                    int map_index = pid_for_file % PID_OFF_MAP_SIZE;
                                    off_t prev = pid_offsets[map_index];
                                    int rf = open(fname, O_RDONLY);
                                    if (rf >= 0) {
                                        off_t end = lseek(rf, 0, SEEK_END);
                                        if (end == -1) end = 0;
                                        if (end > prev) {
                                            off_t len = end - prev;
                                            if (lseek(rf, prev, SEEK_SET) == prev) {
                                                char *all = malloc((size_t)len + 1);
                                                if (all) {
                                                    ssize_t got = read(rf, all, (size_t)len);
                                                    if (got < 0) got = 0;
                                                    all[got] = '\0';
                                                    pid_offsets[map_index] = end;

                                                    time_t now = time(NULL);
                                                    struct tm *tm_info = localtime(&now);
                                                    char tstr[64];
                                                    strftime(tstr, sizeof(tstr), "%Y-%m-%d %H:%M:%S", tm_info);
                                                    char header[256];
                                                    snprintf(header, sizeof(header), "\"%s\" , %s :",
                                                            tt->mw_cmds[m].cmd, tstr);

                                                    if (tt->lines_count >= MAX_LINES) {
                                                        free(tt->lines[0]);
                                                        memmove(&tt->lines[0], &tt->lines[1], sizeof(char*)*(MAX_LINES-1));
                                                        memmove(&tt->is_command[0], &tt->is_command[1], sizeof(int)*(MAX_LINES-1));
                                                        tt->lines_count--;
                                                    }
                                                    tt->lines[tt->lines_count] = strdup(header);
                                                    tt->is_command[tt->lines_count++] = 0;

                                                    if (tt->lines_count >= MAX_LINES) {
                                                        free(tt->lines[0]);
                                                        memmove(&tt->lines[0], &tt->lines[1], sizeof(char*)*(MAX_LINES-1));
                                                        memmove(&tt->is_command[0], &tt->is_command[1], sizeof(int)*(MAX_LINES-1));
                                                        tt->lines_count--;
                                                    }
                                                    tt->lines[tt->lines_count] = strdup("----------------------------------------------------");
                                                    tt->is_command[tt->lines_count++] = 0;

                                                    append_text(tt, all, (int)strlen(all));

                                                    if (tt->lines_count >= MAX_LINES) {
                                                        free(tt->lines[0]);
                                                        memmove(&tt->lines[0], &tt->lines[1], sizeof(char*)*(MAX_LINES-1));
                                                        memmove(&tt->is_command[0], &tt->is_command[1], sizeof(int)*(MAX_LINES-1));
                                                        tt->lines_count--;
                                                    }
                                                    tt->lines[tt->lines_count] = strdup("----------------------------------------------------");
                                                    tt->is_command[tt->lines_count++] = 0;

                                                    free(all);
                                                }
                                            }
                                        }
                                        close(rf);
                                    }
                                    if (ti == active) scroll_to_cursor(tt);
                                } 
                                else if (r == 0) 
                                {
                                    close(fd);
                                    tt->mw_cmds[m].fd[0] = -1;
                                } 
                                else if (r < 0 && errno != EAGAIN && errno != EWOULDBLOCK) 
                                {
                                    close(fd);
                                    tt->mw_cmds[m].fd[0] = -1;
                                }
                            }
                        }

                        int openFound = 0;
                        for (int m = 0; m < tt->mw_n; ++m)
                            if (tt->mw_cmds[m].fd[0] >= 0) openFound = 1;

                        if (!openFound) 
                        {
                            for (int m = 0; m < tt->mw_n; ++m) 
                            {
                                if (tt->mw_cmds[m].pid > 0) waitpid(tt->mw_cmds[m].pid, NULL, 0);
                                if (tt->mw_cmds[m].fd[0] >= 0) close(tt->mw_cmds[m].fd[0]);
                                if (tt->mw_cmds[m].fd[1] >= 0) close(tt->mw_cmds[m].fd[1]);
                                if (tt->mw_cmds[m].cmd) free(tt->mw_cmds[m].cmd);
                                tt->mw_cmds[m].cmd = NULL;
                                tt->mw_cmds[m].fd[0] = -1;
                                tt->mw_cmds[m].fd[1] = -1;
                                tt->mw_cmds[m].pid = -1;
                            }
                            tt->mw_n = 0;
                            tt->mw_maxfd = -1;
                        }
                    }
                }
            }
        } 
        else 
        {
            nanosleep(&ts, NULL);
        }

        blink_counter++;
        if (blink_counter % 10 == 0) cursor_visible = !cursor_visible;
        draw_ui(display, win, gc, font, &tabs[active], active, tab_count,
                search_mode, search_buf, search_len, search_cursor);
    }

    if (xic) XDestroyIC(xic);
    if (xim) XCloseIM(xim);
    XFreeFont(display, font);
    XCloseDisplay(display);
    return 0;
}