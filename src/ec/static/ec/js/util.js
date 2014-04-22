function map(f, xs) {
	return xs.map(function(x,_,_) { return f(x) })
};

function find(f, xs) {
	for (var i in xs) {
		var x = xs[i];
		if (f(x)) {
			return x;
		}
	}
	return null;
};