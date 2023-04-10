include "wn.mm";
include "wa.mm";
include "lear.mm";
include "ax-a1.mm";
include "lbtr.mm";
include "ax-r4.mm";
include "le3tr1.mm";

theorem gomaex3h8(wvp: $term$ p, wvq: $term$ q, wvu: $term$ u, wvw: $term$ w) {
  assume gomaex3h8.19: $|- u = ( p ' ^ q )$;
  assume gomaex3h8.20: $|- w = q '$;





  do {
    wvp;
    wn;
    #;
    wvq;
    wa;
    #;
    wvq;
    wn;
    #;
    wn;
    #;
    wvu;
    wvw;
    wn;
    @1;
    wvq;
    @3;
    @0;
    wvq;
    lear;
    wvq;
    ax-a1;
    lbtr;
    gomaex3h8.19;
    wvw;
    @2;
    gomaex3h8.20;
    ax-r4;
    le3tr1;
  };

  return $|-$ $u =< w '$;
}
