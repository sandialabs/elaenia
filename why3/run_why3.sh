#!/bin/bash

# direct why3 to use the local overlay for plugin files
export WHY3LIB=./install/lib/why3
export WHY3DATA=./install/share/why3

why3 $@
