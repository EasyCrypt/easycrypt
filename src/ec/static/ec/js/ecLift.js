var Range = ace.require("ace/range").Range
var Search = ace.require("ace/search").Search

function ecLift(editor) {
  function range_of_point(p) {
    return new Range(p.row, p.column, p.row, p.column);
  }

  editor._step = 0;
  editor.points = [(new Range(0,0,0,0)).end];
  editor.last_point = function() {
    return this.points[this.points.length - 1];
  }

  editor.loading_marker = null;
  editor.loaded_marker  = null;

  editor.next_point = function() {
    var search = new Search();
    search.setOptions({
      start: range_of_point(this.last_point()),
      needle: /\.$|\.\W/,
      regExp: true
    });
    return search.find(this.getSession()).end;
  }

  editor.step = function(conn) {
    var from = this.last_point();
    var to = this.next_point();
    this.points = this.points.concat([to]);

    var stmt_range = new Range(from.row, from.column, to.row, to.column);
    conn.send(this.getSession().getTextRange(stmt_range));

    var loaded_range = new Range(0, 0, to.row, to.column);
    if (this.loading_marker != null)
      this.getSession().removeMarker(this.loading_marker);
    this.loading_marker = this.getSession().addMarker(loaded_range, "ace_loading", "text", false);
  }
  editor.setStep = function(newStep) {
    this._step = newStep;
  }
}