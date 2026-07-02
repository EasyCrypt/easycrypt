module DoubleIf = {
    proc f() = {
        var x: int;

        if ((fun x => x) true) {}
        x <- 0;
        if (false) {}
    }
    proc g() = {
        var x: int;

        if (false) {}
        if (true) {}
        x <- 0;
    }
}.

equiv dif: DoubleIf.f ~ DoubleIf.g: true ==> true.
proof.
proc.
eager if; expect 4.
abort.

module DoubleWhile = {
    proc f() = {
        var x: int;

        x <- 0;
        while ((fun x => x) true) {}
        while (false) {}
    }
    proc g() = {
        var x: int;

        while (false) {}
        x <- 0;
        while (true) {}
    }
}.

equiv dwl: DoubleWhile.f ~ DoubleWhile.g: true ==> true.
proof.
proc.
eager while (true); expect 6.
abort.
