include "wo.mm";
include "wn.mm";
include "wa.mm";
include "comcom3.mm";
include "mhlem1.mm";
include "ax-a2.mm";
include "lan.mm";
include "ax-r2.mm";
include "2an.mm";
include "leao2.mm";
include "leao3.mm";
include "ler2an.mm";
include "lel2or.mm";
include "oran2.mm";
include "anor3.mm";
include "lbtr.mm";
include "mhlem.mm";

theorem mhlem2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume mh.1: $|- a C c$;
  assume mh.2: $|- a C d$;
  assume mh.3: $|- b C c$;
  assume mh.4: $|- b C d$;





  do {
    wva;
    wvc;
    wo;
    wvc;
    wn;
    #;
    wvb;
    wn;
    #;
    wo;
    wa;
    #;
    wvb;
    wvd;
    wo;
    #;
    wva;
    wn;
    #;
    wvd;
    wn;
    #;
    wo;
    #;
    wa;
    #;
    wa;
    wva;
    @0;
    wa;
    #;
    wvc;
    @1;
    wa;
    #;
    wo;
    #;
    wvb;
    @5;
    wa;
    #;
    wvd;
    @4;
    wa;
    #;
    wo;
    #;
    wa;
    @8;
    @11;
    wa;
    @9;
    @12;
    wa;
    wo;
    @2;
    @10;
    @7;
    @13;
    wva;
    wvc;
    @1;
    mh.1;
    wvb;
    wvc;
    mh.3;
    comcom3;
    mhlem1;
    @7;
    @3;
    @5;
    @4;
    wo;
    #;
    wa;
    @13;
    @6;
    @14;
    @3;
    @4;
    @5;
    ax-a2;
    lan;
    wvb;
    wvd;
    @4;
    mh.4;
    wva;
    wvd;
    mh.2;
    comcom3;
    mhlem1;
    ax-r2;
    2an;
    @8;
    @11;
    @9;
    @12;
    @8;
    @11;
    wo;
    @0;
    wvb;
    wo;
    #;
    @5;
    wva;
    wo;
    #;
    wa;
    #;
    @9;
    @12;
    wo;
    wn;
    #;
    @8;
    @17;
    @11;
    @8;
    @15;
    @16;
    @0;
    wva;
    wvb;
    leao2;
    wva;
    @0;
    @5;
    leao3;
    ler2an;
    @11;
    @15;
    @16;
    wvb;
    @5;
    @0;
    leao3;
    @5;
    wvb;
    wva;
    leao2;
    ler2an;
    lel2or;
    @17;
    @9;
    wn;
    #;
    @12;
    wn;
    #;
    wa;
    @18;
    @15;
    @19;
    @16;
    @20;
    wvc;
    wvb;
    oran2;
    wvd;
    wva;
    oran2;
    2an;
    @9;
    @12;
    anor3;
    ax-r2;
    lbtr;
    mhlem;
    ax-r2;
  };

  return $|- ( ( ( a v c ) ^ ( c ' v b ' ) ) ^ ( ( b v d ) ^ ( a ' v d ' ) ) ) = ( ( ( a ^ c ' ) ^ ( b ^ d ' ) ) v ( ( c ^ b ' ) ^ ( d ^ a ' ) ) )$;
}
