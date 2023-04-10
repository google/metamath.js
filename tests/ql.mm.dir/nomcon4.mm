include "wid1.mm";
include "wn.mm";
include "wid2.mm";
include "wid4.mm";
include "wid3.mm";
include "nomcon1.mm";
include "nomb41.mm";
include "nomb32.mm";
include "3tr1.mm";

theorem nomcon4(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wid1;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wid2;
    wva;
    wvb;
    wid4;
    @1;
    @0;
    wid3;
    wvb;
    wva;
    nomcon1;
    wva;
    wvb;
    nomb41;
    @1;
    @0;
    nomb32;
    3tr1;
  };

  return $|- ( a ==4 b ) = ( b ' ==3 a ' )$;
}
