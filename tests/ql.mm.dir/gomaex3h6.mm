include "wn.mm";
include "wi1.mm";
include "leid.mm";
include "ax-a1.mm";
include "lbtr.mm";
include "ax-r4.mm";
include "le3tr1.mm";

theorem gomaex3h6(wvm: $term$ m, wvn: $term$ n, wvp: $term$ p, wvq: $term$ q) {
  assume gomaex3h6.17: $|- m = ( p ' ->1 q )$;
  assume gomaex3h6.18: $|- n = ( p ' ->1 q ) '$;





  do {
    wvp;
    wn;
    wvq;
    wi1;
    #;
    @0;
    wn;
    #;
    wn;
    #;
    wvm;
    wvn;
    wn;
    @0;
    @0;
    @2;
    @0;
    leid;
    @0;
    ax-a1;
    lbtr;
    gomaex3h6.17;
    wvn;
    @1;
    gomaex3h6.18;
    ax-r4;
    le3tr1;
  };

  return $|- m =< n '$;
}
