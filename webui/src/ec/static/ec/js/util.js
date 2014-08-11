/*                     List processing helpers                    */
/* -------------------------------------------------------------- */
function find(f, xs) {
	for (var i in xs) {
		var x = xs[i];
		if (f(x)) {
			return x;
		}
	}
	return null;
};

function find_idx(f, xs) {
  for (var i in xs) {
    if (f(xs[i])) {
      return parseInt(i);
    }
  }
  return -1;
};

/* -------------------------------------------------------------- */
function neq(x) {
  return function(y) {
    return x !== y;
  }
}

/* CSRF (https://docs.djangoproject.com/en/dev/ref/contrib/csrf/) */
/* -------------------------------------------------------------- */
function set_up_csrf_token() {
  var csrftoken = $.cookie('csrftoken');
  function csrfSafeMethod(method) {
    return (/^(GET|HEAD|OPTIONS|TRACE)$/.test(method));
  }
  $.ajaxSetup({
    crossDomain: false,
    beforeSend: function(xhr, settings) {
      if (!csrfSafeMethod(settings.type)) {
          xhr.setRequestHeader("X-CSRFToken", csrftoken);
      }
    }
  });
}

/*                      Node creation helpers                     */
/* -------------------------------------------------------------- */

function row() { // Extra arguments are appended as inner nodes
  var node = $('<div>').addClass('row');
  for (var i = 0; i < arguments.length; i++) {
    node.append(arguments[i]);
  }
  return node;
};

function col(size, offset) { // Extra arguments are appended as inner nodes
  function class_for_device(device) {
    var base = "col-" + device + "-";
    var size_class = base + size;
    if (offset) {
      var offset_class = base + "offset-" + offset;
      return size_class + " " + offset_class;
    } else {
      return size_class;
    }
  };
  var devices = ["sm", "md", "lg"];
  var classes = devices.map(class_for_device).join(" ");
  var node = $('<div>').addClass(classes);
  for (var i = 2; i < arguments.length; i++) {
    node.append(arguments[i]);
  }
  return node;
};

function glyph(classes) {
  var node = $('<span>').addClass('glyphicon ' + classes);
  return node;
};

/*                 WebSocket EcConn implementation                */
/* -------------------------------------------------------------- */

var WSEcConn = function() {
  this.srv_addr = "ws://localhost:8888/";
  this.socket = null;
  this.conn_ops = {
      open: null,
      close: null,
      step: null,
      notice: null,
      proof: null,
      error: null
  }
}

WSEcConn.prototype.open = function() {
  this.close();

  this.socket = new WebSocket(this.srv_addr);
  this.socket.onopen = this.conn_ops.open;
  this.socket.onclose = this.conn_ops.close;
  this.socket.onerror = function(e) { console.log("======== [" + addr + "] ERROR\n" + e.data + "========\n"); };
  this.socket.onmessage = function(e) {
    var data = JSON.parse(e.data);
    switch (data.type) {
    case "step":
      if (this.conn_ops.step !== null) this.conn_ops.step(data.step);
      break;
    case "notice":
      if (this.conn_ops.notice !== null) this.conn_ops.notice(data.value);
      break;
    case "proof":
      if (this.conn_ops.proof !== null) this.conn_ops.proof(data.value);
      break;
    case "error":
      if (this.conn_ops.error !== null) this.conn_ops.error(data.value);
      break;
    default:
      console.log("ERROR: no parse from server data");
    }
  }.bind(this);
  return this.socket;
}

WSEcConn.prototype.close = function() {
  if (this.socket !== null) this.socket.close();
}

WSEcConn.prototype.eval = function(stmt) {
  this.socket.send(stmt + "\n");
}

WSEcConn.prototype.undo = function(step) {
  this.socket.send("undo " + step + ".\n");
}

WSEcConn.prototype.onOpen = function(callback) {
  this.conn_ops.open = callback;
}
WSEcConn.prototype.onClose = function(callback) {
  this.conn_ops.close = callback;
}
WSEcConn.prototype.onStep = function(callback) {
  this.conn_ops.step = callback;
}
WSEcConn.prototype.onNotice = function(callback) {
  this.conn_ops.notice = callback;
}
WSEcConn.prototype.onProof = function(callback) {
  this.conn_ops.proof = callback;
}
WSEcConn.prototype.onError = function(callback) {
  this.conn_ops.error = callback;
}

/* -------------------------------------------------------------- */
