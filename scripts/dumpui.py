#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, lxml.etree as xml, StringIO as sio

# --------------------------------------------------------------------
class Object(object):
    def __init__(self, **kw):
        self.__dict__.update(kw)

# --------------------------------------------------------------------
SCHEMA = '''\
<xsd:schema xmlns:xsd="http://www.w3.org/2001/XMLSchema">
  <xsd:element name="node" type="nodetype"/>

  <xsd:complexType name="nodetype">
    <xsd:sequence>
      <xsd:element name="node" type="nodetype" minOccurs="0" maxOccurs="unbounded" />
    </xsd:sequence>
    <xsd:attribute name="data" type="xsd:string" />
  </xsd:complexType>
</xsd:schema>
'''

# --------------------------------------------------------------------
class Node(object):
    def __init__(self, data, children):
        self._data     = data
        self._children = children

    def dump(self, stream = sys.stderr, indent = 0):
        print >>stream, '%s%s' % ('  ' * indent, self._data)
        for child in self._children:
            child.dump(stream, indent + 1)

# --------------------------------------------------------------------
def gettree(doc):
    schema = xml.XMLSchema(xml.parse(sio.StringIO(SCHEMA)))
    doc    = xml.parse(sio.StringIO(doc))

    if not schema.validate(doc):
        return None

    def buildtree(root):
        data     = root.get('data')
        children = map(buildtree, root)
        return Node(data, children)

    return buildtree(doc.getroot())

# --------------------------------------------------------------------
def _main():
    gettree(open('dump-test.xml').read()).dump()

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
