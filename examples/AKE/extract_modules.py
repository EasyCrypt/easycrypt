#!/usr/bin/python

import re
import os

def get_modules(filename):
  start_re = re.compile('^module[\s]+([\w]+)')
  end_re = re.compile('^\}.')
  module = {}
  in_module = False
  with open(filename) as file_contents:
    for line in file_contents:
      res = start_re.findall(line)
      if len(res) == 1:
        #print "START"
        #print res[0]
        module['name'] = res[0]
        module['content'] = [line]
        in_module = True
      elif in_module:
        module['content'].append(line)
        if end_re.match(line):
          #print "END"
          in_module = False
          yield module

modules = list(get_modules('AKE_proof.ec'))
if not (os.path.isdir('modules')):
  os.mkdir('modules')
for m in modules:
  filename = "modules/%s.ec" % m['name']
  print "Writing file `%s'" % filename
  f = open(filename, "w")
  f.write("".join(m['content']))
