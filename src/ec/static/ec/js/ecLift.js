var Range = ace.require("ace/range").Range
var Search = ace.require("ace/search").Search

function ecLift(editor) {
  function _range_of_point(p) {
    return new Range(p.row, p.column, p.row, p.column);
  }

  editor.step = 0;
  editor.points = [(new Range(0,0,0,0)).end];
  editor.last_point = function() {
    return this.points[this.points.length - 1];
  }
  editor.loading_marker = null;
  editor.loaded_marker  = null;

  editor.online = function() {
    this._online = true;
  }

  editor.offline = function() {
    this._online = false;
  }

  editor.next_point = function() {
    var search = new Search();
    search.setOptions({
      start: _range_of_point(this.last_point()),
      needle: /\.$|\.\W/,
      regExp: true
    });
    return search.find(this.getSession()).end;
  }

  editor.do_step = function(conn) {
    if (this._online) {
      var from = this.last_point();
      var to = this.next_point();
      var stmt_range = new Range(from.row, from.column, to.row, to.column);
      conn.send(this.getSession().getTextRange(stmt_range));

      this.points = this.points.concat([to]);
      this.update_markers();
    }
  }

  editor.set_step = function(newStep) {
    this.step = newStep;
    if (newStep !== 0)
      this.update_markers();
  }

  editor.update_markers = function() {
    if (this.loading_marker !== null)
      this.getSession().removeMarker(this.loading_marker);
    if (this.loaded_marker !== null)
      this.getSession().removeMarker(this.loaded_marker);

    var loaded_pt = this.points[this.step];
    var loaded_range = new Range(0, 0, loaded_pt.row, loaded_pt.column);
    this.loaded_marker = this.getSession().addMarker(loaded_range, "ace_loaded", "text");

    var loading_pt = this.points[this.points.length-1];
    var loading_range = new Range(loaded_pt.row, loaded_pt.column, loading_pt.row, loading_pt.column);
    this.loading_marker = this.getSession().addMarker(loading_range, "ace_loading", "text");
  }
}