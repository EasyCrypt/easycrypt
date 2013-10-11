// --------------------------------------------------------------------
Array.prototype.peek = function() {
    if (this.length > 0)
        return this[this.length-1];
    return undefined;
}

// --------------------------------------------------------------------
function EasyCryptEditor(name) {
    this.widgets = {
        code    : $('#' + name + "-code"),
        feedback: $('#' + name + "-feedback"),
        status  : $('#' + name + "-status"),
        log     : $('#' + name + "-log"),
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
    
    var url = "ws://localhost:8080/engine";
    this.socket = new WebSocket(url, "easycrypt");
    this.socket.onopen    = this.onopen.bind(this);
    this.socket.onclose   = this.onclose.bind(this);
    this.socket.onerror   = this.onerror.bind(this);
    this.socket.onmessage = this.onmessage.bind(this);

    var onnext   = this._on_next.bind(this);
    var onprev   = this._on_prev.bind(this);
    var oncursor = this._on_cursor.bind(this);

    var km = {
        "Ctrl-Down" : function (cm) { onnext(); },
        "Ctrl-Up"   : function (cm) { onprev(); },
        "Ctrl-Space": function (cm) { oncursor(); },
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
}

EasyCryptEditor.prototype.onclose = function(event){
    this.socket = null;
    this.log('The connection to the EasyCrypt engine has been closed', 'error', false)
    this.setStatus('error');
}

EasyCryptEditor.prototype.onerror = function(event){
    this.socket = null;
    this.log('The connection to the EasyCrypt engine failed', 'error', false);
    this.setStatus('error');
}

EasyCryptEditor.prototype.onmessage = function(event){
    try {
        var json = JSON.parse(event.data);
    } catch (e) {
        return;
    }

    if (json.status == "error") {
        var end = this.endofsent.pop();

        this.widgets.feedback.text($.format("> error: {0}\n", json.message));

/*
        var pos = { line : json.end.line-1,
                   start : json.start_err,
                     end : json.end_err };
        this.setROMark_error(pos);
*/
    }

    else if (json.status == 'ok') {
        var end = this.endofsent.peek();

        end.pundo = json.pundo;
        this.setROMark(end);
        this.widgets.feedback.text($.format("> {0}\n", json.message));
    }

    else if (json.status == "undo"){
        this.widgets.feedback.text('')
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
    if (autoclear)
        setTimeout(function () { tag.remove(); }, 3000);
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
    if (this.socket == null) return ;

    var prev = this.endofsent.peek() || {line: 0, ch: 1};
    var end  = this.findStatement(prev);

    if (end) {
        this.endofsent.push(end);
        this.clearERRMark();
        var json = JSON.stringify({ mode     : "forward",
                                    contents : end.contents });
        this.socket.send(json);
    }
}

EasyCryptEditor.prototype._on_prev = function() {
    if (this.socket == null) return ;

    if (this.endofsent.length == 0)
        return ;

    var posend   = this.endofsent.pop();
    var posstart = this.endofsent.peek();

    this.clearERRMark();
    this.setROMark(posstart);

    var json = JSON.stringify({ mode : "undo", data : posend.pundo });
    this.socket.send(json);
}

EasyCryptEditor.prototype._on_cursor = function() {
    if (this.socket == null) return ;

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
