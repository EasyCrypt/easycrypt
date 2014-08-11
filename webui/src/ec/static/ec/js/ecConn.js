/*
 * EcConn interface:
 *
 *  open  : () -> ()
 *  close : () -> ()
 *  eval  : String -> ()
 *  undo  : Int -> ()
 *
 *  onOpen   : (() -> ()) -> ()
 *  onClose  : (() -> ()) -> ()
 *  onStep   : (Int -> ()) -> ()
 *  onNotice : (String -> ()) -> ()
 *  onProof  : (String -> ()) -> ()
 *  onError  : (String -> ()) -> ()
 *
 */


/* ---------------------------------------------------------------- */
function ecLiftEditor(editor, conn /* : EcConn */) {
  var Range = ace.require("ace/range").Range
  var Search = ace.require("ace/search").Search

  function _point(row, col) {
    return (new Range(row, col, row, col).start)
  }
  function _range_of_point(p) {
    return new Range(p.row, p.column, p.row, p.column);
  }
  function _compare_points(p1, p2) {
    return _range_of_point(p1).compare(p2.row, p2.column);
  }

  /* -------------------------------------------------------------- */
  editor.online = false;

  editor.step = 0;
  editor._start = _point(0, 0);
  editor.points = [editor._start];

  editor._loading = false;
  editor.markers = [];

  /* -------------------------------------------------------------- */
  editor.loading_point = function() {
    return this.points[this.points.length - 1];
  }

  editor.loaded_point = function() {
    return this.points[this.step];
  }

  /* -------------------------------------------------------------- */
  editor.prev_stop_from = function(point) {
    var search = new Search();
    search.setOptions({
      backwards: true,
      start: _range_of_point(point),
      needle: /\.$|\.\W/g,
      wrap: false,
      regExp: true
    });
    var stop = search.find(this.getSession());
    return (stop ? stop.end : this._start);
  }

  editor.next_stop_from = function(point) {
    var search = new Search();
    search.setOptions({
      start: _range_of_point(point),
      needle: /\.$|\.\W/,
      wrap: false,
      regExp: true
    });
    var stop = search.find(this.getSession());
    return (stop && stop.end);
  }

  editor.next_stop = function() {
    return this.next_stop_from(this.loading_point());
  }

  /* -------------------------------------------------------------- */
  editor.do_step = function() {
    if (this.online) {
      var from = this.loading_point();
      var to = this.next_stop();
      if (to !== null) {
        var stmt_range = Range.fromPoints(from, to);
        this.conn.eval(this.getSession().getTextRange(stmt_range));

        this.points = this.points.concat([to]);
        this._loading = true;
        this.update_markers();
      }
    }
  }

  editor.undo_to_step = function(step) {
    if (this.online && !this._loading && step >= 0) {
      this.points.splice(step+1);
      this.step = step;
      this._loading = true;
      this.conn.undo(step);
      this.update_markers();
    }
  }

  editor.undo_step = function() {
    this.undo_to_step(this.step-1);
  }

  editor.step_until_cursor = function(until_prev) {
    until_prev = until_prev || false;
    if (this.online) {
      var from = this.loading_point();
      var cursor = this.getCursorPosition();
      var prev_stop = this.prev_stop_from(cursor);

      var search = new Search();
      search.setOptions({
        range: Range.fromPoints(prev_stop, cursor),
        needle: /^\W*$/,
        wrap: false,
        regExp: true
      });
      var cursor_after_stop =
        cursor.row === prev_stop.row && search.find(this.getSession());

      switch (_compare_points(from, cursor)) {
      case 0:
        break;
      case -1:  // Step backward (undo)
        if (until_prev || cursor_after_stop) {
          var to = prev_stop;
        } else {
          var to = this.next_stop_from(cursor);
        }
        for (var i = 0; i < this.points.length; i++) {
          if (_compare_points(this.points[i], to) === 0) {
            this.undo_to_step(i);
            break;
          }
        }
        break;
      case 1:   // Step forward
        if (until_prev || cursor_after_stop) {
          var to = prev_stop;
        } else {
          var to = this.next_stop_from(cursor);
        }
        if (to === null) {   // At the end of the document
          while (this.next_stop_from(from) !== null) {
            this.do_step();
            from = this.loading_point();
          }
        } else {
          while (_compare_points(from, to) > 0) {
            this.do_step();
            from = this.loading_point();
          }
        }
        break;
      }
    }
  }

  /* -------------------------------------------------------------- */
  editor.set_step = function(newStep) {
    this.step = newStep;
    if (newStep !== 0)
      this.update_markers();
    if (newStep === this.points.length-1) {
      this._loading = false;
    }
  }

  /* -------------------------------------------------------------- */
  editor.update_markers = function() {
    var session = this.getSession();

    for (var i = 0; i < this.markers.length; i++)
      session.removeMarker(this.markers[i]);

    var loaded_pt = this.loaded_point();
    var loading_pt = this.loading_point();

    var loaded_range = Range.fromPoints(this._start, loaded_pt);
    var loading_range = Range.fromPoints(loaded_pt, loading_pt);

    this.markers = [ session.addMarker(loaded_range, "ace_loaded"),
                     session.addMarker(loading_range, "ace_loading") ];
  }

  /* -------------------------------------------------------------- */
  editor.on("change", function(e) {
    var from = this.loading_point();
    if ((Range.fromPoints(this._start, from)).intersects(e.data.range)) {
      this.step_until_cursor(true);
    }
  }.bind(editor));

  /* -------------------------------------------------------------- */
  editor.conn = conn;

  function toHTML(data) {
    return data.replace(/&/g, "&amp;").replace(/</g, "&lt;")
               .replace(/>/g, "&gt;").replace(/\n/g, "<br />");
  }

  var results = $("#results");
  editor.conn.onOpen(function() {
    this.online = true;
    results.html("");
  }.bind(editor));
  editor.conn.onClose(function() {
    this.online = false;
    results.text("<offline>");
  }.bind(editor));
  editor.conn.onStep(editor.set_step.bind(editor));
  editor.conn.onNotice(function(text) {
    results.html(toHTML(text));
  }.bind(editor));
  editor.conn.onProof(function(text) {
    results.html(toHTML(text));
  }.bind(editor));
  editor.conn.onError(function(text) {
    results.html(toHTML("ERROR: " + text));
  }.bind(editor));

  editor.conn.open();
}
