include "wn.mm";
include "leid.mm";
include "ax-r4.mm";
include "le3tr1.mm";

theorem gomaex3h9(wvq: $term$ q, wvw: $term$ w, wvx: $term$ x) {
  assume gomaex3h9.20: $|- w = q '$;
  assume gomaex3h9.21: $|- x = q$;





  do {
    wvq;
    wn;
    #;
    @0;
    wvw;
    wvx;
    wn;
    @0;
    leid;
    gomaex3h9.20;
    wvx;
    wvq;
    gomaex3h9.21;
    ax-r4;
    le3tr1;
  };

  return $|- w =< x '$;
}
