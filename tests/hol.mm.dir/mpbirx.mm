include "hb.mm";
include "ax-cb2.mm";
include "eqcomx.mm";
include "ax-eqmp.mm";

theorem mpbirx(ta: term A, tb: term B, tr: term R) {
  assume mpbirx.1: |- "B : bool";
  assume mpbirx.2: |- "R |= A";
  assume mpbirx.3: |- "R |= ( ( = B ) A )";





  do {
    ta;
    tb;
    tr;
    mpbirx.2;
    hb;
    tb;
    ta;
    tr;
    mpbirx.1;
    ta;
    tr;
    mpbirx.2;
    ax-cb2;
    mpbirx.3;
    eqcomx;
    ax-eqmp;
  };

  return |- "R |= B";
}
