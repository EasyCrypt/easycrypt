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
      return i;
    }
  }
  return -1;
};

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
