{ fetchFromGitHub
, lib
, which
, ocamlPackages
, version ? "2.4.1"
, sha256  ? "o6Wqg0IvOX5bGRk+KZogqqtsJ0gwAN10FHyUA26Q9EE="
}:

let
  pname = "alt-ergo";
  inherit version;

  src = fetchFromGitHub {
    owner = "OCamlPro";
    repo = pname;
    rev = version;
    inherit sha256;
  };

  useDune2 = true;
in

let alt-ergo-lib = ocamlPackages.buildDunePackage rec {
  pname = "alt-ergo-lib";
  inherit version src useDune2;
  configureFlags = pname;
  nativeBuildInputs = [ which ];
  buildInputs = with ocamlPackages; [ dune-configurator ];
  propagatedBuildInputs = with ocamlPackages; [ num ocplib-simplex stdlib-shims zarith ];
}; in

let alt-ergo-parsers = ocamlPackages.buildDunePackage rec {
  pname = "alt-ergo-parsers";
  inherit version src useDune2;
  configureFlags = pname;
  nativeBuildInputs = [ which ocamlPackages.menhir ];
  propagatedBuildInputs = [ alt-ergo-lib ] ++ (with ocamlPackages; [ camlzip psmt2-frontend ]);
}; in

ocamlPackages.buildDunePackage {

  inherit pname version src useDune2;

  configureFlags = pname;

  nativeBuildInputs = [ which ocamlPackages.menhir ];
  buildInputs = [ alt-ergo-parsers ocamlPackages.cmdliner ];

  meta = {
    description = "High-performance theorem prover and SMT solver";
    homepage    = "https://alt-ergo.ocamlpro.com/";
    license     = lib.licenses.ocamlpro_nc;
    maintainers = [ lib.maintainers.thoughtpolice ];
  };
}
