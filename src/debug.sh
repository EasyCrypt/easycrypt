#! /bin/bash

(echo "source debug.cmd"; cat) | ocamldebug "$@" __ignore__
