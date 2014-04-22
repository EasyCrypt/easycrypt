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
