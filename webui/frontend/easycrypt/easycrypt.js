function EasyCryptEditor(name) {
    this.widgets = {
        prev    : $('#' + name + "-prev"),
        next    : $('#' + name + "-next"),
        test    : $('#' + name + "-test"),
        code    : $('#' + name + "-code"),
        feedback: $('#' + name + "-feedback"),        
    };

    this.name     = name;
    this.position = -1;
    this.romark   = null;
    this.editor   = null;

    this.createWidget();
}

// --------------------------------------------------------------------
// Widget creation
EasyCryptEditor.prototype.createWidget = function() {
    if (this.editor)
        return ;

    var foldFunc = CodeMirror.newFoldFunction(CodeMirror.braceRangeFinder);

    var options = {
               mode: "text/x-easycrypt",
        lineNumbers: true,
         indentUnit: 4,
            tabMode: "shift",
      matchBrackets: true,
       lineWrapping: true,
          extraKeys: {"Ctrl-Q": function(cm){foldFunc(cm, cm.getCursor().line);}},
    };

    this.editor = CodeMirror.fromTextArea(this.widgets.code[0], options);
    this.editor.on("gutterClick", foldFunc);
    foldFunc(this.editor, 0);

    this.widgets.test.click(this._on_test.bind(this));
    this.widgets.next.click(this._on_next.bind(this));
    this.widgets.prev.click(this._on_prev.bind(this));
}

// --------------------------------------------------------------------
// Read-only marker management
EasyCryptEditor.prototype.clearROMark = function() {
    if (this.romark)
      this.romark.clear();
    this.romark = null;
}

EasyCryptEditor.prototype.setROMark = function(end) {
    var opts = {
        className: this.name + '-read-only',
         readOnly: true,
    };

    this.clearROMark();
    this.romark = this.editor.markText({ line: 0, ch: 0 }, end, opts);
}

// --------------------------------------------------------------------
// Buttons callbacks
EasyCryptEditor.prototype._on_test = function() {
    var line = this.editor.getLine(0);
    var l = 0;
    var statement;
    for (var i = 1; i < line.length; i++) {
    	var o = this.editor.getTokenAt({ line: l, ch: i});
    	if (o.type == "punctuation" && o.string == '.') {
    		statement = line.substr(0,i);
    	}
    }
    alert(statement);
    //alert(o.start + " " + o.end + " " + o.string + " " + o.type);
}

EasyCryptEditor.prototype._on_next = function() {
    if (this.position < this.editor.lineCount()-1) {
        this.position++;
        var line = this.editor.getLine(this.position);
        this.widgets.feedback
            .append("STATEMENT SENT: " + (this.position+1) +
                    " " + line + "\n");
    }
    this.setROMark({ line: this.position+1, ch: 0 });
}

EasyCryptEditor.prototype._on_prev = function() {
    if (this.position >= 0) {
        this.position--;
        var line = this.editor.getLine(this.position);
        this.widgets.feedback
            .append("LINE SENT: " + (this.position+1) +
                    " " + line + "\n");
        this.setROMark({ line: this.position+1, ch: 0 });
    }
}

// --------------------------------------------------------------------
EasyCryptEditor.prototype.findStatement = function(line) {
    var counter = line.length-1;
    for (var c = 0; c < counter; c++ ) {
        if (line[c] == '.' && line[c+1] == ' ')
        	return line.substr(0,c);
    }
}
