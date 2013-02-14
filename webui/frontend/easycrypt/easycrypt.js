// --------------------------------------------------------------------
Array.prototype.peek = function() {
	if (this.length > 0)
		return this[this.length-1];
	return undefined;
}

// --------------------------------------------------------------------
function EasyCryptEditor(name) {
    this.widgets = {
        prev    : $('#' + name + "-prev"),
        next    : $('#' + name + "-next"),
        test    : $('#' + name + "-test"),
        code    : $('#' + name + "-code"),
        feedback: $('#' + name + "-feedback"),        
    };

    this.name      = name;
    this.endofsent = [];
    this.init      = 0;
    this.romark    = null;
    this.editor    = null;

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
      inclusiveRight: false,
    };

    this.clearROMark();
    if (end)
    	this.romark = this.editor.markText({ line: 0, ch: 0 }, end, opts);
}

// --------------------------------------------------------------------
// Buttons callbacks
EasyCryptEditor.prototype._on_test = function() {
	var myWebSocket = new WebSocket("ws://echo.websocket.org");
	var message = "what do you want to send";
	myWebSocket.onopen = function(evt) { 
		alert("Connection is opening...");
		alert("SENT : " + message);
		myWebSocket.send(message);
	};
	myWebSocket.onclose = function(evt) { alert("Connection is closed"); };
	myWebSocket.onmessage = function(evt) { 
		alert("SERVER: " + evt.data);
		myWebSocket.close();
		};
}

EasyCryptEditor.prototype._on_next = function() {
	prev = this.endofsent.peek() || {line: 0, ch: 1};
	end  = this.findStatement(prev);

	if (end) {
		this.widgets.feedback
			.append($.format("STATEMENT SENT: {0} {1}\n",
					         end.line+1, end.contents));
		this.endofsent.push(end);
		this.setROMark(end);
	}
}

EasyCryptEditor.prototype._on_prev = function() {
	if (this.endofsent.length == 0)
		return ;

	var posend   = this.endofsent.pop();
	var posstart = this.endofsent.peek();

	this.setROMark(posstart);

	this.widgets.feedback
    	.append($.format("LINE SENT: {0} {1}\n",
    					 posend.line+1, posend.contents));
}

// --------------------------------------------------------------------
EasyCryptEditor.prototype.findStatement = function(position) {
	var contents = "";
	var current  = {     line: position.line ,
			               ch: position.ch   ,
			         contents: ""            };
	
	while (current.line < this.editor.lineCount()) {
		if (current.ch-1 == this.editor.getLine(current.line).length) {
			contents += " ";
			++current.line;
			current.ch = 1;
			continue ;
		}

		var token = this.editor.getTokenAt(current);

		contents += token.string;
		current.ch = token.end+1;
		if (token.string == "." && token.type == "punctuation") {
			current.contents = contents;			
			break ;
		}
	}

	return current.contents ? current : undefined;
}
