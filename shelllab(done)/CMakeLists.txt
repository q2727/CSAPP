cmake_minimum_required(VERSION 3.26)
project(shelllab C)

set(CMAKE_C_STANDARD 11)

add_executable(shelllab tsh.c csapp.c csapp.h)
