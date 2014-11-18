/* ------------------------------------------------------------------------ */
var Points = {
	compare: function(p1, p2) {
		return (p1.line != p2.line) ? (p1.line - p2.line) : (p1.ch - p2.ch);
	},
	
	copy: function(p) {
	    return { line: p.line, ch: p.ch };
	}
}

/* ------------------------------------------------------------------------ */
var CodePoint = function(p, uuid) {
	return { line: p.line, ch: p.ch, uuid: uuid };
}

/* ------------------------------------------------------------------------ */
function create_editor(manager) {
	options = {};
	options.mode              = "text/x-easycrypt";
	options.lineNumbers       = true;
	options.indentUnit        = 4;
	options.tabMode           = "shift";
	options.matchBrackets     = true;
	options.styleSelectedText = true;
	options.styleActiveLine   = true;
	options.gutters           = ["CodeMirror-linenumbers", "edit-point"];

	editor = document.getElementById("editor");
	editor = CodeMirror.fromTextArea(editor, options);

	editor.myoptions = options;
	editor.driver    = manager.driver;

    /* ---------------------------------------------------------------------- */
    editor._reset_state = function() {
        this.ecstart  = { ch: 0, line: 0 };
        this.ecend    = { ch: 0, line: 0 };
        this.ecdone   = { ch: 0, line: 0 };
        this.ecproc   = { ch: 0, line: 0 };
        this.ecpoints = [];
        this.ecmark   = { done: null, locked: null };
        this.ecerr    = null;
        this.ecuuid   = this.driver.uuid;
        this.ecundo   = null;
        this.ecfatal  = false;
        this.ecsynced = (this.driver.state == 'ec:waiting');
        
        this.getAllMarks().forEach(function (m) { m.clear(); });
        
        if (this.ecsynced)
            this.ecpoints.push(new CodePoint(this.ecstart, this.driver.uuid));
    }.bind(editor);
    
    /* ---------------------------------------------------------------------- */
    editor.set_contents = function(contents) {
        this.swapDoc(new CodeMirror.Doc(contents || '', this.myoptions.mode));
        this.focus(); this._reset_state();
    }.bind(editor);

    /* ---------------------------------------------------------------------- */
    editor.set_contents(null);
    
	/* ---------------------------------------------------------------------- */
	editor.driver.prompt.connect(function (uuid) {
		if (this.ecsynced || this.ecfatal) return ;

		this.ecsynced = true;
		this.ecuuid   = uuid;
		
		if (this.ecpoints.length == 0)
			this.ecpoints.push(new CodePoint(this.ecstart, uuid));

		if (this.ecundo !== null) {
		    if (Points.compare(this.ecdone, this.ecproc) != 0)
		        this.fatal_error();
		    this.ecundo = null;
		    while (this.ecpoints.length) {
		        var last = this.ecpoints[this.ecpoints.length-1];
		        if (last.uuid == this.ecuuid)
		            break ;
		        this.ecpoints.pop();
		        if (this.ecpoints.length < 2)
		            break ;
		    }
		    if (!this.ecpoints.length)
		        this.fatal_error();
		    var last = this.ecpoints[this.ecpoints.length-1];
		    this.ecdone = Points.copy(last);
            this.ecproc = Points.copy(last);
            this.ecend  = Points.copy(last);
		} else if (Points.compare(this.ecdone, this.ecproc) < 0) {
			this.ecpoints.push(new CodePoint(this.ecproc, uuid));
			this.ecdone = Points.copy(this.ecproc);
		}

		this._maybe_send_next_sentence();
    	this._update_markers();
	}.bind(editor));
    
	/* ---------------------------------------------------------------------- */
	editor.driver.ecerror.connect(function (start, end, msg) {
        if (this.ecfatal) return ;
		if (this.ecsynced || Points.compare(this.ecdone, this.ecend) >= 0) return ;

		var cp = this.indexFromPos(this.ecdone);
		var p1 = this.posFromIndex(cp + start);
		var p2 = this.posFromIndex(cp + end);

		this.ecend  = Points.copy(this.ecdone);
		this.ecproc = Points.copy(this.ecdone);
		this._set_err_mark(p1, p2);
		this._update_markers();
	}.bind(editor));
	
	/* ---------------------------------------------------------------------- */
	editor.driver.exited.connect(function () {
		this._reset_state();
	}.bind(editor));

    /* ---------------------------------------------------------------------- */
    editor._fatal_error = function() {
        if (!this.ecfatal) {
            this.ecfatal = true;
            this.driver.close();
        }
        throw 'ec-fatal-error';
    }.bind(editor);
	
	/* ---------------------------------------------------------------------- */
    editor.next_sentence = function() {
        if (this.ecfatal) return false;
        
    	var cursor = this.getSearchCursor(/\.$|\.\W/g, this.ecend, false);

    	if (!cursor.findNext())
    		return false;
    	this.ecend = Points.copy(cursor.to());
    	this._maybe_send_next_sentence();
    	this._update_markers();
    	return true;
    }.bind(editor);

	/* ---------------------------------------------------------------------- */
    editor.prev_sentence = function() {
        if (this.ecfatal)
            return false;
        if (!this.ecsynced || this.ecpoints.length < 2)
            return false;

        var last = this.ecpoints[this.ecpoints.length-2];    	
    	this.ecundo   = last.uuid;
    	this.ecsynced = false;
    	this._send_undo(this.ecundo);
        this._update_markers();
        return true;
    }.bind(editor);
    
	/* ---------------------------------------------------------------------- */
    editor.to_cursor = function() {
        if (this.ecfatal || this.ecundo !== null) return false;

        var cpos   = this.getCursor();
    	var cursor = this.getSearchCursor(/\.$|\.\W/g, cpos, false);

    	cpos = cursor.findPrevious() ? cursor.to() : Points.copy(this.ecstart);

    	if (Points.compare(this.ecend, cpos) < 0) {    	
        	this.ecend = Points.copy(cpos);
        	this._maybe_send_next_sentence();
        	this._update_markers();
        	return true;
    	}
    	
    	if (Points.compare(this.ecend, cpos) > 0) {
    	    if (Points.compare(this.ecdone, this.ecend) != 0)
    	        return false;
    	    for (var i = this.ecpoints.length; i != 0; --i) {
    	        var p = this.ecpoints[i-1];
    	        console.log(p, cpos);
    	        if (Points.compare(cpos, p) == 0) {
    	            this.ecundo   = p.uuid;
    	            this.ecsynced = false;
    	            this._send_undo(this.ecundo);
    	            this._update_markers();
    	            return true;
    	        }
    	    }
    	}
    	
    	return false;
    }

    /* ---------------------------------------------------------------------- */
    editor._clear_markers = function() {
        ['done', 'locked'].forEach(function (x) {
            if (this.ecmark[x])
                this.ecmark[x].clear();
            this.ecmark[x] = null;            
        }.bind(this));
        this.clearGutter('edit-point');
    }.bind(editor);

    /* ---------------------------------------------------------------------- */
    editor._update_markers = function() {
    	this._clear_markers();
        this.ecmark.done   = this.markText(this.ecstart, this.ecdone, { className: 'editor-done' });
    	this.ecmark.locked = this.markText(this.ecdone , this.ecend , { className: 'editor-locked' });

    	if (Points.compare(this.ecstart, this.ecend) < 0) {
            var marker = $('<div class="edit-point">●</div>')[0];
        	this.setGutterMarker(this.ecend.line, "edit-point", marker);
    	}
    }.bind(editor);

	/* ---------------------------------------------------------------------- */
    editor._clear_err_mark = function() {
    	if (this.ecerr)
    		this.ecerr.clear();
    	this.ecerr = null;
    }.bind(editor);
    
	/* ---------------------------------------------------------------------- */
    editor._set_err_mark = function(p1, p2) {
    	this._clear_err_mark();
        this.ecerr = this.markText(p1, p2, { className: 'editor-error' });		
    }.bind(editor);
        
    /* ---------------------------------------------------------------------- */
    editor._maybe_send_next_sentence = function() {
    	if (!this.ecsynced || this.ecfatal)
    		return false;
    	if (Points.compare(this.ecdone, this.ecend) >= 0)
    		return false;

    	var cursor   = this.getSearchCursor(/\.$|\.\W/g, this.ecdone, false);
    	var sentence = null;
    	
      	if (!cursor.findNext()) {
      		this.ecdone = Points.copy(this.ecend);
      		this.ecproc = Points.copy(this.ecend);
      		return false;
      	}
    	
    	this.ecproc   = Points.copy(cursor.to());
    	this.ecsynced = false;

    	sentence = this.getRange(this.ecdone, this.ecproc);
    	this.driver.send(sentence);
    }.bind(editor);

    /* ---------------------------------------------------------------------- */
    editor._send_undo = function(uiid) {
        this.driver.send($.format('undo {0}.', this.ecundo));
    }.bind(editor);

    /* ---------------------------------------------------------------------- */
    editor.on("change", editor._clear_err_mark);
    
    /* ---------------------------------------------------------------------- */
    editor.on("beforeChange", function(target, event) {
        if (Points.compare(event.from, this.ecend) < 0)
            event.cancel();
    }.bind(editor));

    /* ---------------------------------------------------------------------- */
	return editor;
}
