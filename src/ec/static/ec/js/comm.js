/* ---------------------------------------------------------------- */
var Conn = function(editor) {
  this.srv_addr = "ws://localhost:8888/";
  this.socket = null;
  this.results = $("#results");
  this.editor = editor;

  this.init();
}

Conn.prototype.init = function(editor) {
  if (this.socket !== null) this.close();
  this.open(this.srv_addr);
}

Conn.prototype.open = function(addr) {
  this.socket = new WebSocket(addr);

  function debug(data) {
    //console.log("\n\n======== [" + addr + "] (" + data.type + ")\n");
  }
  function toHTML(data) {
    return data.replace(/&/g, "&amp;").replace(/</g, "&lt;")
               .replace(/>/g, "&gt;").replace(/\n/g, "<br />");
  }

  this.socket.onopen = function(e) {
    console.log("[+] Opened '" + addr + "'");
    this.editor.online = true;
    this.results.html("");
  }.bind(this);
  this.socket.onclose = function(e) {
    console.log("[+] Closed '" + addr + "'");
    this.editor.online = false;
    this.results.text("<offline>");
  }.bind(this);
  this.socket.onmessage = function(e) {
    var data = JSON.parse(e.data);
    switch (data.type) {
    case "step":
      debug(data);
      this.editor.set_step(data.step);
      break;
    case "notice":
    case "proof":
      debug(data);
      this.results.html(toHTML(data.value));
      break;
    case "error":
      debug(data);
      break;
    default:
      console.log("ERROR");
    }
  }.bind(this);
  this.socket.onerror = function(e) { console.log("======== [" + addr + "] ERROR\n" + e.data + "========\n"); };
  return this.socket;
}

Conn.prototype.close = function() {
  this.socket.close();
}

Conn.prototype.send = function(data) {
  this.socket.send(data + "\n");
}


/* ---------------------------------------------------------------- */
function ecLiftEditor(editor) {
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
  editor.conn = null;
  editor.online = false;

  editor.step = 0;
  editor._start = _point(0, 0);
  editor.points = [editor._start];

  editor._loading = false;
  editor.loading_marker = null;
  editor.loaded_marker  = null;

  /* -------------------------------------------------------------- */
  editor.loading_point = function() {
    return this.points[this.points.length - 1];
  }

  editor.loaded_point = function() {
    return this.points[this.step];
  }

  /* -------------------------------------------------------------- */
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
        this.conn.send(this.getSession().getTextRange(stmt_range));

        this.points = this.points.concat([to]);
        this._loading = true;
        this.update_markers();
      }
    }
  }

  editor.undo = function(step) {
    if (this.online && !this._loading && step >= 0) {
      this.points.splice(step+1);
      this.step = step;
      this._loading = true;
      this.conn.send("undo " + step + ".");
      this.update_markers();
    }
  }

  editor.undo_step = function() {
    this.undo(this.step-1);
  }

  editor.step_until_cursor = function() {
    if (this.online) {
      var from = this.loading_point();
      var cursor = this.getCursorPosition();
      switch (_compare_points(from, cursor)) {
      case 0:
        break;
      case -1:
        var to = this.next_stop_from(cursor);
        for (var i = 0; i < this.points.length; i++) {
          if (_compare_points(this.points[i], to) === 0) {
            this.undo(i);
            break;
          }
        }
        break;
      case 1:
        var to = this.next_stop_from(cursor);
        if (to === null) {
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
    if (newStep === this.points.length-1)
      this._loading = false;
  }

  /* -------------------------------------------------------------- */
  editor.update_markers = function() {
    var session = this.getSession();

    if (this.loading_marker !== null)
      session.removeMarker(this.loading_marker);
    if (this.loaded_marker !== null)
      session.removeMarker(this.loaded_marker);

    var loaded_pt = this.loaded_point();
    var loaded_range = Range.fromPoints(this._start, loaded_pt);
    this.loaded_marker = session.addMarker(loaded_range, "ace_loaded", "text");

    var loading_pt = this.loading_point();
    var loading_range = Range.fromPoints(loaded_pt, loading_pt);
    this.loading_marker = session.addMarker(loading_range, "ace_loading", "text");
  }

  /* -------------------------------------------------------------- */
  editor.conn = new Conn(editor);
}
