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

/*                      Node creation helpers                     */
/* -------------------------------------------------------------- */

// Extra arguments are appended as inner nodes
function row() {
  var node = $('<div>').addClass('row');
  for (var i = 0; i < arguments.length; i++) {
    node.append(arguments[i]);
  }
  return node;
};

// Extra arguments are appended as inner nodes
function col(size, offset) {
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
