include "wo.mm";
include "wn.mm";
include "wi1.mm";
include "wa.mm";
include "lear.mm";
include "bltr.mm";
include "lecon.mm";
include "ax-r4.mm";
include "le3tr1.mm";

theorem gomaex3h4(wvc: $term$ c, wvd: $term$ d, wvj: $term$ j, wvk: $term$ k, wvp: $term$ p, wvq: $term$ q, wvr: $term$ r) {
  assume gomaex3h4.11: $|- r = ( ( p ' ->1 q ) ' ^ ( c v d ) )$;
  assume gomaex3h4.15: $|- j = ( c v d ) '$;
  assume gomaex3h4.16: $|- k = r$;





  do {
    wvc;
    wvd;
    wo;
    #;
    wn;
    wvr;
    wn;
    wvj;
    wvk;
    wn;
    wvr;
    @0;
    wvr;
    wvp;
    wn;
    wvq;
    wi1;
    wn;
    #;
    @0;
    wa;
    @0;
    gomaex3h4.11;
    @1;
    @0;
    lear;
    bltr;
    lecon;
    gomaex3h4.15;
    wvk;
    wvr;
    gomaex3h4.16;
    ax-r4;
    le3tr1;
  };

  return $|- j =< k '$;
}
