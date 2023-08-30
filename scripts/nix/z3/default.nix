{ nixpkgs ? <nixpkgs> }:

with import nixpkgs { };

let python = python3; in

stdenv.mkDerivation rec {
  pname   = "z3";
  version = "4.12.2";
  sha256  = "sha256-DTgpKEG/LtCGZDnicYvbxG//JMLv25VHn/NaF307JYA=";

  src = fetchFromGitHub {
    owner = "Z3Prover";
    repo = pname;
    rev = "-${version}";
    sha256 = sha256;
  };

  strictDeps = true;

  nativeBuildInputs = [ python ];
  propagatedBuildInputs = [ python.pkgs.setuptools ];
  enableParallelBuilding = true;

  configurePhase = "${python.pythonForBuild.interpreter} scripts/mk_make.py --prefix=$out\ncd build";

  doCheck = true;
  checkPhase = ''
    make test
    ./test-z3 -a
  '';

  postInstall = ''
    mkdir -p $dev $lib
    mv $out/lib $lib/lib
    mv $out/include $dev/include
  '';

  outputs = [ "out" "lib" "dev" ];

  meta = with lib; {
    description = "A high-performance theorem prover and SMT solver";
    homepage = "https://github.com/Z3Prover/z3";
    changelog = "https://github.com/Z3Prover/z3/releases/tag/z3-${version}";
    license = licenses.mit;
    platforms = platforms.unix;
    maintainers = with maintainers; [ thoughtpolice ttuegel ];
  };
}
