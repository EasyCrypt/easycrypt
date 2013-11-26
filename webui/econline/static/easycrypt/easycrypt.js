// --------------------------------------------------------------------
Array.prototype.peek = function() {
    if (this.length > 0)
        return this[this.length-1];
    return undefined;
}

// --------------------------------------------------------------------
function EasyCryptEditor(name, url) {
    this.widgets = {
        code     : $('#' + name + "-code"),
        feedback : $('#' + name + "-feedback"),
        status   : $('#' + name + "-status"),
        log      : $('#' + name + "-log"),
        operators: $('#' + name + "-operators"),
    };

    this.name      = name;
    this.url       = url;
    this.endofsent = [];
    this.init      = 0;
    this.romark    = null;
    this.errmark   = null;  
    this.editor    = null;
    this.socket    = null;
    this.job       = null;
    
    this.createWidget();
}

// --------------------------------------------------------------------
// Widget creation
EasyCryptEditor.prototype.createWidget = function() {
    if (this.editor)
        return ;
    
    this.socket = new WebSocket(this.url, "easycrypt");
    this.socket.onopen    = this.onopen.bind(this);
    this.socket.onclose   = this.onclose.bind(this);
    this.socket.onerror   = this.onerror.bind(this);
    this.socket.onmessage = this.onmessage.bind(this);

    var onnext = this._on_next.bind(this);
    var onprev = this._on_prev.bind(this);

    var km = {
        'Ctrl-N' : function (cm) { onnext(); },
        'Ctrl-P'   : function (cm) { onprev(); },
    };

    var options = {
               mode: "text/x-easycrypt",
        lineNumbers: true,
         indentUnit: 4,
            tabMode: "shift",
      matchBrackets: true,
       lineWrapping: true,
          autofocus: true,
          extraKeys: km,
    };

    this.editor = CodeMirror.fromTextArea(this.widgets.code[0], options);
    this.editor.setSize(null, this.widgets.feedback.height() + 10);

    $(window).mouseup(function () {
        this.editor.setSize(null, this.widgets.feedback.height() + 10);
    }.bind(this));

    this.setStatus('unknown');
}

//---------------------------------------------------------------------
EasyCryptEditor.prototype.onopen = function(event){
    this.log('You are now connected to the EasyCrypt engine', 'success', true);
    this.setStatus('ready');
    
    var editorState = this.editor.getStateAfter(this.widgets.feedback.height() + 10, true);
    
    var numberOfOperators = editorState.operatorsList.length;
	var numberOfTheories = editorState.theoriesList.length;
	
		
	var j=0;
	var i=0;
    //while(j<numberOfTheories) {
    while(i<numberOfOperators) {
    try {
    	if(editorState.theoriesList[j].startLine < editorState.operatorsList[i].line) {
			    this.printTheory(editorState, j);
	    		j++;
	    }
	    else {
	    	if(editorState.operatorsList[i].line > editorState.theoriesList[j].startLine && 
	    	  editorState.operatorsList[i].line < editorState.theoriesList[j].endLine) {
	    	  	this.printOperatorIndented(editorState, i);
	    		i++;
	    		if(i>=numberOfOperators) 
	    			for(j; j<numberOfTheories; j++)
	    				this.printTheory(editorState, j); 		
	    	}
	        else {	    	
	        	this.printOperator(editorState, i);
	    		i++; 
	    		if(i>=numberOfOperators) 
	    			for(j; j<numberOfTheories; j++)
	    				this.printTheory(editorState, j); 
	    	}
		} 
	}catch(TypeError) {
		j--;
		for(i; i<numberOfOperators; i++)
			if(editorState.operatorsList[i].line > editorState.theoriesList[j].startLine && 
	    	  	editorState.operatorsList[i].line < editorState.theoriesList[j].endLine)
	    	  	this.printOperatorIndented(editorState, i);
	    	else			
				this.printOperator(editorState, i);
	 }
	}
}

EasyCryptEditor.prototype.printOperator = function(editorState, i){
	this.widgets.operators.append("... <span class='icon icon-plus-sign'/> "
	    			+ editorState.operatorsList[i].name 
	    			+ " {line: " + editorState.operatorsList[i].line + "}"  
	    			+ "<div />");
}

EasyCryptEditor.prototype.printOperatorIndented = function(editorState, i){
	this.widgets.operators.append("........ <span class='icon icon-plus-sign'/> "
	    			+ editorState.operatorsList[i].name 
	    			+ " {line: " + editorState.operatorsList[i].line + "}"  
	    			+ "<div />");
}

EasyCryptEditor.prototype.printTheory = function(editorState, j){
	this.widgets.operators.append("... <span class='icon icon-text-width'/> "
				    		+ editorState.theoriesList[j].name 
	    					+ " {start: " + editorState.theoriesList[j].startLine 
				    		+ " , end: " + editorState.theoriesList[j].endLine + "}"  
	    					+ "<div />");	
}

EasyCryptEditor.prototype.onclose = function(event){
    this.socket = null;
    this.job    = null;
    this.log('The connection to the EasyCrypt engine has been closed', 'error', false)
    this.setStatus('error');
}

EasyCryptEditor.prototype.onerror = function(event){
    this.socket = null;
    this.job    = null;
    this.log('The connection to the EasyCrypt engine failed', 'error', false);
    this.setStatus('error');
}

EasyCryptEditor.prototype.onmessage = function(event){
    var job  = this.job;
    var json = JSON.parse(event.data);

    this.job = null;
    this.setStatus('ready');
    this.widgets.feedback.text('')

    if (json.status == 'error') {
        /*
        var pos = { line : json.end.line-1,
                   start : json.start_err,
                     end : json.end_err };
        this.setErrorMask(pos);
        */

        this.endofsent.pop()
        this.setROMark(this.endofsent.peek());
        this.widgets.feedback.text($.format("error: {0}\n", json.message));
    }

    if (json.status == 'ok') {
        end = this.endofsent.peek();
        end.pundo = json.pundo;
        this.setROMark(end);
        this.widgets.feedback.text($.format("{0}\n", json.message));
        
        var match = json.message.match(/added operator:/g);
        var length = json.message.length;
        if(match != null) {
	        this.widgets.operators.append($.format("> {0}\n", json.message.substring(17, length-3)));
	        }
    }

    if (json.status == 'undo') {
        this.endofsent.pop();
        this.setROMark(this.endofsent.peek());
        this.widgets.feedback.text($.format("{0}\n", json.message));
    }
}

// --------------------------------------------------------------------
// Read-only marker management
EasyCryptEditor.prototype.clearROMark = function() {
    if (this.romark)
      this.romark.clear();
    this.romark = null;
}

EasyCryptEditor.prototype.clearErrorMark = function() {
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
    if (end) {
        if (end.line == this.editor.lineCount()-1 &&
            end.ch-1 == this.editor.getLine(end.line).length)
        {
            this.editor.replaceRange('\n', end, end);
        }
        this.romark = this.editor.markText({ line: 0, ch: 0 }, end, opts);
    }
}

EasyCryptEditor.prototype.setErrorMark = function(pos) {
    var opts = {
           className: this.name + '-error',
      inclusiveRight: false, 
       clearOnEnter : true,
    };

    if (pos) {
        this.errmark = this.editor.markText(
            { line: pos.line, ch: pos.start }, 
            { line: pos.line, ch: pos.end },
            opts);
    }
}

// --------------------------------------------------------------------
// Status
EasyCryptEditor.prototype.log = function(msg, level, autoclear) {
    var tag = $(document.createElement('div'))
                .attr({'class': $.format('alert alert-dismissable alert-{0}', level)})
                .append($(document.createElement('button'))
                          .attr({        'type': 'button',
                                        'class': 'close' ,
                                 'data-dismiss': 'alert' ,
                                  'aria-hidden': 'true'  })
                          .append('&times;'))
                .append(msg);

    this.widgets.log.append(tag);
    if (autoclear) {
        setTimeout(function () {
            tag.fadeOut('fast', function() { tag.remove(); });
        }, 3000);
    }
}

EasyCryptEditor.prototype.setStatus = function(status) {
    var icon = 'question-sign';

    if (status == 'ready'  ) icon = 'ok-sign';
    if (status == 'working') icon = 'fire'
    if (status == 'error'  ) icon = 'remove'

    this.widgets.status.removeAttr('class');
    this.widgets.status.addClass('icon');
    this.widgets.status.addClass('icon-' + icon);
}

// --------------------------------------------------------------------
// Callbacks
EasyCryptEditor.prototype._on_next = function() {
    if (this.socket == null || this.job != null) return ;

    var prev = this.endofsent.peek() || {line: 0, ch: 1};
    var end  = this.findStatement(prev);

    if (end) {
        var json = JSON.stringify({ mode     : "forward",
                                    contents : end.contents });

        this.endofsent.push(end);
        this.clearErrorMark();
        this.socket.send(json);
        this.job = json;
        this.setStatus('working');
    }
}

EasyCryptEditor.prototype._on_prev = function() {
    if (this.socket == null || this.job != null) return ;

    if (this.endofsent.length == 0)
        return ;

    var posend = this.endofsent.peek();
    var json   = JSON.stringify({ mode : 'undo', data : posend.pundo });

    this.clearErrorMark();
    this.socket.send(json);
    this.job = json;
    this.setStatus('working');
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
