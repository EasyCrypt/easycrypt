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
        prevcur : $('#' + name + "-prevcur"),
        code    : $('#' + name + "-code"),
        feedback: $('#' + name + "-feedback"),        
    };

    this.name      = name;
    this.endofsent = [];
    this.init      = 0;
    this.romark    = null;
    this.errmark   = null;	
    this.editor    = null;
    this.socket    = null;
    
    this.createWidget();
}

// --------------------------------------------------------------------
// Widget creation
EasyCryptEditor.prototype.createWidget = function() {
    if (this.editor)
        return ;
    
    var url = "ws://localhost:8080";
    this.socket = new WebSocket(url, "echo-protocol");
    this.socket.onopen = this.onopen.bind(this);
    this.socket.onerror = this.onerror.bind(this);
    this.socket.onmessage = this.onmessage.bind(this);
    
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

    this.widgets.next.click(this._on_next.bind(this));
    this.widgets.prev.click(this._on_prev.bind(this));
    this.widgets.prevcur.click(this._on_prevcur.bind(this));
}

//---------------------------------------------------------------------
EasyCryptEditor.prototype.onopen = function(event){
		this.widgets.feedback
			.append("Connected\n");
	}

EasyCryptEditor.prototype.onerror = function(event){
	this.widgets.feedback
		.append("Coonection not available." + event);
}

EasyCryptEditor.prototype.onmessage = function(event){
	//this.widgets.feedback
	//.append(event.data + "\n");
	try{
		var json = JSON.parse(event.data);
	} catch (e) {
		console.log('This doesn\'t look like a valid JSON: ', event);
		return;
		}
	if (json.mode == "error"){
		this.widgets.feedback
			.append($.format("{0} at line {1}\n", 
						json.message, json.end.line));
		var pos = { line : json.end.line-1,
				   start : json.start_err,
				     end : json.end_err };
		this.setROMark_error(pos);
		this.endofsent.pop();
		this.widgets.next.disabled = true;
	}
	else if (json.mode == "undo"){
		this.widgets.feedback
			.append(json.data + "\n");
	}
	else{
		this.setROMark(end);
		this.widgets.feedback
		.append($.format("STATEMENT SENT: {0} {1}\n",
						json.end.line+1, json.end.contents));
	}
		
}

// --------------------------------------------------------------------
// Read-only marker management
EasyCryptEditor.prototype.clearROMark = function() {
    if (this.romark)
      this.romark.clear();
    this.romark = null;
}

EasyCryptEditor.prototype.clearERRMark = function() {
    if (this.errmark)
      this.errmark.clear();
    this.errmark = null;
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

EasyCryptEditor.prototype.setROMark_error = function(pos) {
    var opts = {
           className: this.name + '-read-only-error',
      inclusiveRight: false, 
       clearOnEnter : true,
    };

    if (pos)
    	this.errmark = this.editor.markText({ line: pos.line, ch: pos.start }, 
    						 				{ line: pos.line, ch: pos.end },
    						 				opts);
}

// --------------------------------------------------------------------
// Buttons callbacks

EasyCryptEditor.prototype._on_next = function() {
	prev = this.endofsent.peek() || {line: 0, ch: 1};
	end  = this.findStatement(prev);

	if (end) {
		/*this.widgets.feedback
			.append($.format("STATEMENT SENT: {0} {1}\n",
					         end.line+1, end.contents));*/
		//alert(end.contents + " " + end.line + " " + end.ch);
		this.endofsent.push(end);
		this.clearERRMark();
		var json = JSON.stringify({ mode : "forward",
									 end : end 
								 /*id_line : end.line,
									data : end.contents*/});
		this.socket.send(json);
	}
}

EasyCryptEditor.prototype._on_prev = function() {
	if (this.endofsent.length == 0)
		return ;

	var posend   = this.endofsent.pop();
	var posstart = this.endofsent.peek();

	this.clearERRMark();
	this.setROMark(posstart);

	/*this.widgets.feedback
    	.append($.format("LINE SENT: {0} {1}\n",
    					 posend.line+1, posend.contents));*/
	var json = JSON.stringify({ mode : "undo", data : posend.contents});
	this.socket.send(json);
}

EasyCryptEditor.prototype._on_prevcur = function() {
	
	var cursor = this.editor.getCursor();
	var history = this.endofsent.peek();
	this.clearERRMark();
	
	while (cursor.line < history.line) 
			history = this.endofsent.pop();
	// for different statement on the same line
	while (cursor.line == this.endofsent.peek().line && cursor.ch < this.endofsent.peek().ch)
		this.endofsent.pop();
		
	this.clearROMark();
	if (cursor.line == history.line)
		this.setROMark(this.endofsent.peek());
	else {
		this.setROMark(history);
		this.endofsent.push(history);
	}
		
	
	
	//alert(history.contents + " " + history.line + " " + history.ch);
	
    
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
