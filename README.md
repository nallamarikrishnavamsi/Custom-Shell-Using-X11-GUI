# Custom-Shell-Using-X11-GUI

# MyTerm_X11

MyTerm_X11 is a custom graphical terminal application implemented in C using the X11
windowing system. It replicates core functionality of Unix shells while integrating
process management and GUI-based interaction.

## Features
- X11-based graphical terminal interface
- Multi-tab shell sessions
- Execution of external commands using fork() and execvp()
- Input/output redirection (<, >) and command pipelines (|)
- Command history, auto-completion, and multiWatch support
- Unicode and multiline input handling
- Signal handling (Ctrl+C, Ctrl+Z)

## Design Documentation
Detailed system design and implementation details are provided in:
- `DESIGNDOC.pdf`

## Prerequisites
- GCC or Clang with POSIX support
- X11 development headers (`libX11-dev` on Debian/Ubuntu, `libX11-devel` on Fedora,
  `xorg-x11-devel` on Arch, or XQuartz SDK on macOS)

## Build
```bash
gcc -std=c11 -Wall -Wextra -O2 MyTerm_X11.c -o myterm -lX11
