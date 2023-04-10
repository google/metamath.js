include "wi5.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "df-i5.mm";
include "ran.mm";
include "comanr1.mm";
include "comcom6.mm";
include "com2or.mm";
include "fh1r.mm";
include "wf.mm";
include "an32.mm";
include "anidm.mm";
include "ax-r2.mm";
include "ancom.mm";
include "ax-r1.mm";
include "dff.mm";
include "lan.mm";
include "an0.mm";
include "2or.mm";
include "or0.mm";
include "fh4.mm";
include "ax-a2.mm";
include "orabs.mm";
include "fh1.mm";
include "anass.mm";

theorem u5lemaa(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi5;
    #;
    wva;
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
    wva;
    wa;
    #;
    @1;
    @0;
    @7;
    wva;
    wva;
    wvb;
    df-i5;
    ran;
    @8;
    @4;
    wva;
    wa;
    #;
    @6;
    wva;
    wa;
    #;
    wo;
    #;
    @1;
    wva;
    @4;
    @6;
    wva;
    @1;
    @3;
    wva;
    wvb;
    comanr1;
    #;
    wva;
    @3;
    @2;
    wvb;
    comanr1;
    comcom6;
    #;
    com2or;
    wva;
    @6;
    @2;
    @5;
    comanr1;
    comcom6;
    #;
    fh1r;
    @11;
    @1;
    wva;
    @6;
    wa;
    #;
    wo;
    #;
    @1;
    @9;
    @1;
    @10;
    @15;
    @9;
    @1;
    wva;
    wa;
    #;
    @3;
    wva;
    wa;
    #;
    wo;
    #;
    @1;
    wva;
    @1;
    @3;
    @12;
    @13;
    fh1r;
    @19;
    @1;
    wf;
    wo;
    #;
    @1;
    @17;
    @1;
    @18;
    wf;
    @17;
    wva;
    wva;
    wa;
    #;
    wvb;
    wa;
    #;
    @1;
    wva;
    wvb;
    wva;
    an32;
    @21;
    wva;
    wvb;
    wva;
    anidm;
    ran;
    #;
    ax-r2;
    @18;
    @2;
    wva;
    wa;
    #;
    wvb;
    wa;
    #;
    wf;
    @2;
    wvb;
    wva;
    an32;
    @25;
    wvb;
    @24;
    wa;
    #;
    wf;
    @24;
    wvb;
    ancom;
    @26;
    wvb;
    wf;
    wa;
    wf;
    @24;
    wf;
    wvb;
    @24;
    wva;
    @2;
    wa;
    #;
    wf;
    @27;
    @24;
    wva;
    @2;
    ancom;
    ax-r1;
    wf;
    @27;
    wva;
    dff;
    #;
    ax-r1;
    ax-r2;
    lan;
    wvb;
    an0;
    ax-r2;
    ax-r2;
    ax-r2;
    2or;
    @1;
    or0;
    #;
    ax-r2;
    ax-r2;
    @6;
    wva;
    ancom;
    2or;
    @16;
    @1;
    wva;
    wo;
    #;
    @1;
    @6;
    wo;
    #;
    wa;
    #;
    @1;
    wva;
    @1;
    @6;
    @12;
    @14;
    fh4;
    @32;
    wva;
    @31;
    wa;
    #;
    @1;
    @30;
    wva;
    @31;
    @30;
    wva;
    @1;
    wo;
    wva;
    @1;
    wva;
    ax-a2;
    wva;
    wvb;
    orabs;
    ax-r2;
    ran;
    @33;
    wva;
    @1;
    wa;
    #;
    @15;
    wo;
    #;
    @1;
    wva;
    @1;
    @6;
    @12;
    @14;
    fh1;
    @35;
    @20;
    @1;
    @34;
    @1;
    @15;
    wf;
    @34;
    @22;
    @1;
    @22;
    @34;
    wva;
    wva;
    wvb;
    anass;
    ax-r1;
    @23;
    ax-r2;
    @15;
    @27;
    @5;
    wa;
    #;
    wf;
    @36;
    @15;
    wva;
    @2;
    @5;
    anass;
    ax-r1;
    @36;
    @5;
    @27;
    wa;
    #;
    wf;
    @27;
    @5;
    ancom;
    @37;
    @5;
    wf;
    wa;
    #;
    wf;
    @38;
    @37;
    wf;
    @27;
    @5;
    @28;
    lan;
    ax-r1;
    @5;
    an0;
    ax-r2;
    ax-r2;
    ax-r2;
    2or;
    @29;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|- ( ( a ->5 b ) ^ a ) = ( a ^ b )$;
}
