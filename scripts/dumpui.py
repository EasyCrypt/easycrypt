#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, lxml.etree as xml, StringIO as sio

from PyQt4 import QtCore, QtGui, uic

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
    def __init__(self, data, parent):
        self._parent   = parent
        self._data     = data
        self._children = []

        if parent is not None:
            parent._children.append(self)

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

    def buildtree(root, parent = None):
        node     = Node(root.get('data'), parent)
        children = map(lambda e : buildtree(e, node), root)
        return node

    return buildtree(doc.getroot())

# --------------------------------------------------------------------
def trees():
    trees, contents = [], ''
    for line in sys.stdin:
        contents += line
        if line.rstrip('\r\n') == '</node>':
            trees.append(gettree(contents))
            contents = ''
    return trees

# --------------------------------------------------------------------
class NodeTreeModel(QtCore.QAbstractItemModel):
    def __init__(self, node, parent = None):
        QtCore.QAbstractItemModel.__init__(self, parent)
        self.node = node

    def columnCount(self, index):
        return 1

    def rowCount(self, index):
        if not index.isValid():
            return 1
        return len(index.internalPointer()._children)

    def parent(self, index):
        node = index.internalPointer()

        if node._parent is None:
            return QtCore.QModelIndex()
        else:
            node = node._parent
            if node._parent is None:
                return self.createIndex(0, 0, node)
            return self.createIndex(node._parent._children.index(node), 0, node)

    def index(self, row, column, parent):
        assert (row >= 0 and column >= 0)

        if not parent.isValid():
            if row == 0:
                return self.createIndex(row, 0, self.node)
            return QtCore.QModelIndex()

        parent = parent.internalPointer()

        if row < len(parent._children):
            return self.createIndex(row, 0, parent._children[row])
        return QtCore.QModelIndex()

    def data(self, index, role):
        if role == QtCore.Qt.DisplayRole:
            if index.column() == 0:
                return index.internalPointer()._data
        return QtCore.QVariant()

# --------------------------------------------------------------------
class MainWindow(QtGui.QMainWindow):
    def __init__(self):
        QtGui.QMainWindow.__init__(self)
        uic.loadUi('resources/dump.ui', self)

    @QtCore.pyqtSlot(name = 'on_action_Quit_triggered')
    def quit(self):
        self.close()

    def add_tree(self, tree):
        view = QtGui.QTreeView(self)
        view.setAlternatingRowColors(True)
        view.setModel(NodeTreeModel(tree, view))
        view.header().hide()
        view.expand(view.model().index(0, 0, QtCore.QModelIndex()))
        self.tabs.addTab(view, "Dump %.2d" % (1+self.tabs.count(),))

# --------------------------------------------------------------------
def _main():
    appl = QtGui.QApplication(sys.argv)
    wind = MainWindow()

    for tree in trees():
        wind.add_tree(tree)
    wind.show(); exit(appl.exec_())

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
