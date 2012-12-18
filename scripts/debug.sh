#! /bin/bash

(echo "source scripts/debug.cmd"; cat) | ocamldebug "$@" __ignore__
