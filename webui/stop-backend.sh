#! /bin/sh

pserve --pid-file=backend.pid --log-file=backend.log --stop-daemon backend.ini
