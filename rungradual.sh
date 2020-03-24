#!/bin/sh

LIBDIR=$( stack exec -- ghc -- --print-libdir )

stack exec -- gradualdyn -B/$LIBDIR --make $@
