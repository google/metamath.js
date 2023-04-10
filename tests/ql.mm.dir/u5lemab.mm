include "wi5.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "df-i5.mm";
include "ran.mm";
include "comanr2.mm";
include "com2or.mm";
include "comcom6.mm";
include "fh1r.mm";
include "wf.mm";
include "lear.mm";
include "lel2or.mm";
include "df2le2.mm";
include "an32.mm";
include "anass.mm";
include "dff.mm";
include "lan.mm";
include "ax-r1.mm";
include "an0.mm";
include "ax-r2.mm";
include "2or.mm";
include "or0.mm";

theorem u5lemab(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi5;
    #;
    wvb;
    wa;
    wva;
    wvb;
    wa;
    #;
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    wo;
    #;
    @2;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wvb;
    wa;
    #;
    @4;
    @0;
    @7;
    wvb;
    wva;
    wvb;
    df-i5;
    ran;
    @8;
    @4;
    wvb;
    wa;
    #;
    @6;
    wvb;
    wa;
    #;
    wo;
    #;
    @4;
    wvb;
    @4;
    @6;
    wvb;
    @1;
    @3;
    wva;
    wvb;
    comanr2;
    @2;
    wvb;
    comanr2;
    com2or;
    wvb;
    @6;
    @2;
    @5;
    comanr2;
    comcom6;
    fh1r;
    @11;
    @4;
    wf;
    wo;
    @4;
    @9;
    @4;
    @10;
    wf;
    @4;
    wvb;
    @1;
    wvb;
    @3;
    wva;
    wvb;
    lear;
    @2;
    wvb;
    lear;
    lel2or;
    df2le2;
    @10;
    @3;
    @5;
    wa;
    #;
    wf;
    @2;
    @5;
    wvb;
    an32;
    @12;
    @2;
    wvb;
    @5;
    wa;
    #;
    wa;
    #;
    wf;
    @2;
    wvb;
    @5;
    anass;
    @14;
    @2;
    wf;
    wa;
    #;
    wf;
    @15;
    @14;
    wf;
    @13;
    @2;
    wvb;
    dff;
    lan;
    ax-r1;
    @2;
    an0;
    ax-r2;
    ax-r2;
    ax-r2;
    2or;
    @4;
    or0;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|- ( ( a ->5 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) )$;
}
