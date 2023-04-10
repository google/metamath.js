include "wo.mm";
include "wa.mm";
include "leor.mm";
include "leo.mm";
include "anass.mm";
include "tr.mm";
include "lan.mm";
include "cm.mm";
include "leao4.mm";
include "bltr.mm";
include "lea.mm";
include "orcom.mm";
include "lbtr.mm";
include "ler2an.mm";
include "mldual2i.mm";
include "ancom.mm";
include "ror.mm";
include "lelor.mm";
include "letr.mm";
include "lor.mm";
include "lear.mm";
include "ax-a3.mm";
include "ax-a2.mm";
include "2an.mm";
include "leror.mm";
include "le2an.mm";
include "df2le2.mm";
include "or32.mm";
include "ler.mm";
include "3tr.mm";
include "orass.mm";
include "ran.mm";
include "wt.mm";
include "le1.mm";
include "leran.mm";
include "an1r.mm";
include "oridm.mm";
include "mlduali.mm";
include "id.mm";
include "dp34.mm";
include "lel2or.mm";
include "lelan.mm";
include "mldual.mm";
include "ml2i.mm";
include "leao1.mm";
include "or4.mm";
include "2or.mm";
include "mli.mm";
include "ml3.mm";
include "leao3.mm";
include "le2or.mm";
include "3tr1.mm";
include "df-le2.mm";
include "le3tr2.mm";
include "or12.mm";
include "orabs.mm";
include "ml3le.mm";
include "3tr2.mm";
include "bile.mm";
include "leid.mm";
include "lerr.mm";
include "an32.mm";
include "anabs.mm";

theorem xdp43lem(wvd: $term$ d, wve: $term$ e, wvp: $term$ p, wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvc2: $term$ c2, wvp0: $term$ p0, wvp2: $term$ p2) {
  assume xxdp.1: $|- p2 =< ( a2 v b2 )$;
  assume xxdp.c0: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume xxdp.c1: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;
  assume xxdp.c2: $|- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )$;
  assume xxdp.d: $|- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )$;
  assume xxdp.e: $|- e = ( b0 ^ ( a0 v p0 ) )$;
  assume xxdp.p: $|- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )$;
  assume xxdp.p0: $|- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )$;
  assume xxdp.p2: $|- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )$;





  do {
    wvp;
    wva0;
    wvp;
    wo;
    wva0;
    wvb0;
    wvb1;
    wvc2;
    wvc0;
    wvc1;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wvp;
    wva0;
    leor;
    wva0;
    @4;
    wvp;
    wva0;
    @3;
    leo;
    #;
    wvp;
    wvb0;
    wva0;
    wvp0;
    wo;
    #;
    wa;
    #;
    @4;
    wo;
    #;
    @4;
    wvp;
    @7;
    wva0;
    wo;
    #;
    @8;
    wvp;
    @6;
    wvb0;
    wva0;
    wo;
    #;
    wa;
    #;
    @9;
    wvp;
    wva0;
    wvb0;
    wo;
    #;
    wva1;
    wvb1;
    wo;
    #;
    wva2;
    wvb2;
    wo;
    #;
    wa;
    #;
    wa;
    #;
    @11;
    wvp;
    @12;
    @13;
    wa;
    @14;
    wa;
    @16;
    xxdp.p;
    @12;
    @13;
    @14;
    anass;
    tr;
    @16;
    @6;
    @10;
    @16;
    @12;
    wvp0;
    wa;
    #;
    @6;
    @17;
    @16;
    wvp0;
    @15;
    @12;
    xxdp.p0;
    lan;
    cm;
    wvp0;
    @12;
    wva0;
    leao4;
    bltr;
    @16;
    @12;
    @10;
    @12;
    @15;
    lea;
    wva0;
    wvb0;
    orcom;
    lbtr;
    ler2an;
    bltr;
    @11;
    @6;
    wvb0;
    wa;
    #;
    wva0;
    wo;
    @9;
    wva0;
    wvb0;
    @6;
    wva0;
    wvp0;
    leo;
    mldual2i;
    @18;
    @7;
    wva0;
    @6;
    wvb0;
    ancom;
    ror;
    tr;
    lbtr;
    wva0;
    @4;
    @7;
    @5;
    lelor;
    letr;
    @7;
    @4;
    @7;
    wvb0;
    wva0;
    wvb0;
    wa;
    #;
    wvb1;
    wo;
    @1;
    wo;
    #;
    wa;
    #;
    @4;
    @7;
    wvb0;
    wvb1;
    wva0;
    wva1;
    wo;
    #;
    @0;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @21;
    @7;
    wvb0;
    @24;
    wvb0;
    @6;
    lea;
    #;
    @7;
    wvb1;
    @7;
    wo;
    @24;
    @7;
    wvb1;
    leor;
    wvb1;
    @24;
    @7;
    wvb1;
    @23;
    leo;
    #;
    @7;
    @22;
    @7;
    wvb1;
    wo;
    #;
    wa;
    #;
    @24;
    wo;
    #;
    @24;
    @7;
    @29;
    wvb1;
    wo;
    #;
    @30;
    @7;
    @28;
    @22;
    wvb1;
    wo;
    #;
    wa;
    #;
    @31;
    @7;
    @28;
    @32;
    @7;
    wvb1;
    leo;
    @7;
    wvb0;
    wva0;
    @15;
    wo;
    #;
    wa;
    #;
    @32;
    @6;
    @34;
    wvb0;
    wvp0;
    @15;
    wva0;
    xxdp.p0;
    lor;
    lan;
    #;
    @35;
    @34;
    @32;
    wvb0;
    @34;
    lear;
    @34;
    wva0;
    @13;
    wo;
    #;
    @32;
    @15;
    @13;
    wva0;
    @13;
    @14;
    lea;
    #;
    lelor;
    @32;
    @37;
    wva0;
    wva1;
    wvb1;
    ax-a3;
    cm;
    lbtr;
    letr;
    bltr;
    ler2an;
    @33;
    @28;
    @22;
    wa;
    #;
    wvb1;
    wo;
    @31;
    wvb1;
    @22;
    @28;
    wvb1;
    @7;
    leor;
    mldual2i;
    @39;
    @29;
    wvb1;
    @28;
    @22;
    ancom;
    ror;
    tr;
    lbtr;
    wvb1;
    @24;
    @29;
    @27;
    lelor;
    letr;
    @29;
    @24;
    @24;
    @29;
    @23;
    wvb1;
    wo;
    #;
    @24;
    @29;
    @23;
    wvb1;
    @22;
    wa;
    #;
    wo;
    #;
    @40;
    @29;
    @22;
    @0;
    @41;
    wo;
    #;
    wa;
    @42;
    @29;
    @22;
    @43;
    @22;
    @28;
    lea;
    @29;
    wva1;
    wva2;
    wo;
    #;
    wvb1;
    wvb2;
    wo;
    #;
    wa;
    #;
    wva0;
    wva2;
    wo;
    #;
    wvb0;
    wvb2;
    wo;
    #;
    wa;
    #;
    @41;
    wo;
    #;
    wo;
    #;
    @43;
    @29;
    @47;
    @7;
    wvb2;
    wo;
    #;
    wa;
    #;
    @44;
    @41;
    wo;
    #;
    @45;
    wa;
    #;
    wo;
    #;
    @51;
    @29;
    @53;
    @44;
    wva0;
    @13;
    wa;
    #;
    wo;
    #;
    @45;
    wa;
    #;
    wo;
    #;
    @56;
    @29;
    wva0;
    wva2;
    @57;
    wo;
    #;
    wo;
    #;
    @52;
    wa;
    #;
    wva1;
    @61;
    wo;
    #;
    @45;
    wa;
    #;
    wo;
    #;
    @60;
    @22;
    wve;
    wvb1;
    wo;
    #;
    wa;
    #;
    wva0;
    wvd;
    wo;
    #;
    wve;
    wvb2;
    wo;
    #;
    wa;
    #;
    wva1;
    wvd;
    wo;
    #;
    @45;
    wa;
    #;
    wo;
    #;
    @29;
    @66;
    @68;
    @70;
    @69;
    wva1;
    wvd;
    wvb2;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @72;
    @45;
    wve;
    @75;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    @74;
    @68;
    @70;
    @69;
    wva1;
    wva0;
    wve;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @72;
    @45;
    wve;
    @13;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    @82;
    @68;
    @74;
    wva1;
    wvb1;
    wve;
    wo;
    #;
    wa;
    #;
    wve;
    wva1;
    wva0;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wo;
    #;
    @90;
    @68;
    @68;
    @74;
    @68;
    wva1;
    wve;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @96;
    @68;
    @68;
    @97;
    @68;
    @74;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @100;
    @68;
    @68;
    @13;
    wve;
    wo;
    #;
    wa;
    @93;
    wve;
    wo;
    #;
    wa;
    #;
    @103;
    @68;
    @68;
    @104;
    @105;
    wa;
    #;
    wa;
    #;
    @106;
    @108;
    @68;
    @68;
    @107;
    @68;
    @91;
    @93;
    wa;
    #;
    @107;
    @68;
    @93;
    @91;
    wa;
    #;
    @109;
    @22;
    @93;
    @67;
    @91;
    wva0;
    wva1;
    ax-a2;
    wve;
    wvb1;
    ax-a2;
    2an;
    #;
    @93;
    @91;
    ancom;
    tr;
    @91;
    @104;
    @93;
    @105;
    wvb1;
    @13;
    wve;
    wvb1;
    wva1;
    leor;
    leror;
    @93;
    wve;
    leo;
    le2an;
    bltr;
    df2le2;
    cm;
    @106;
    @108;
    @68;
    @104;
    @105;
    anass;
    #;
    cm;
    tr;
    @106;
    @108;
    @103;
    @112;
    @107;
    @102;
    @68;
    @107;
    @97;
    @13;
    @83;
    wa;
    #;
    wo;
    #;
    @102;
    @107;
    @113;
    wva1;
    wo;
    #;
    wve;
    wo;
    #;
    @113;
    @97;
    wo;
    @114;
    @107;
    @83;
    wva1;
    wo;
    #;
    @104;
    wa;
    #;
    @117;
    @13;
    wa;
    #;
    wve;
    wo;
    @116;
    @107;
    @104;
    @117;
    wa;
    @118;
    @105;
    @117;
    @104;
    @105;
    @22;
    wve;
    wo;
    @117;
    @93;
    @22;
    wve;
    wva1;
    wva0;
    ax-a2;
    ror;
    wva0;
    wva1;
    wve;
    or32;
    tr;
    lan;
    @104;
    @117;
    ancom;
    tr;
    wve;
    @13;
    @117;
    wve;
    @83;
    wva1;
    wve;
    wva0;
    leor;
    ler;
    mldual2i;
    @119;
    @115;
    wve;
    @119;
    @13;
    @117;
    wa;
    @115;
    @117;
    @13;
    ancom;
    wva1;
    @83;
    @13;
    wva1;
    wvb1;
    leo;
    #;
    mldual2i;
    tr;
    ror;
    3tr;
    @113;
    wva1;
    wve;
    orass;
    @113;
    @97;
    orcom;
    3tr;
    @97;
    @102;
    @113;
    @97;
    @101;
    leo;
    @113;
    @113;
    @75;
    wa;
    #;
    @102;
    @113;
    @121;
    @121;
    @121;
    @113;
    @113;
    @75;
    @113;
    @83;
    @13;
    wa;
    #;
    @75;
    @122;
    @113;
    @83;
    @13;
    ancom;
    cm;
    @122;
    wva0;
    @35;
    wo;
    #;
    @13;
    wa;
    #;
    @75;
    @83;
    @123;
    @13;
    wve;
    @35;
    wva0;
    wve;
    @7;
    @35;
    xxdp.e;
    @36;
    tr;
    lor;
    ran;
    @124;
    wva0;
    wt;
    @34;
    wa;
    #;
    wo;
    #;
    @13;
    wa;
    #;
    @75;
    @123;
    @126;
    @13;
    @35;
    @125;
    wva0;
    wvb0;
    wt;
    @34;
    wvb0;
    le1;
    leran;
    lelor;
    leran;
    @127;
    @14;
    @57;
    wo;
    #;
    @75;
    @127;
    @15;
    @57;
    wo;
    #;
    @128;
    @127;
    @15;
    wva0;
    wo;
    #;
    @13;
    wa;
    @129;
    @126;
    @130;
    @13;
    @126;
    wva0;
    @34;
    wo;
    #;
    wva0;
    wva0;
    wo;
    #;
    @15;
    wo;
    #;
    @130;
    @125;
    @34;
    wva0;
    @34;
    an1r;
    lor;
    @133;
    @131;
    wva0;
    wva0;
    @15;
    orass;
    cm;
    @133;
    @34;
    @130;
    @132;
    wva0;
    @15;
    wva0;
    oridm;
    ror;
    wva0;
    @15;
    orcom;
    tr;
    3tr;
    ran;
    @15;
    wva0;
    @13;
    @38;
    mlduali;
    tr;
    @15;
    @14;
    @57;
    @13;
    @14;
    lear;
    leror;
    bltr;
    @128;
    @61;
    wvb2;
    wo;
    #;
    @75;
    wva2;
    wvb2;
    @57;
    or32;
    @75;
    @134;
    wvd;
    @61;
    wvb2;
    xxdp.d;
    ror;
    cm;
    tr;
    lbtr;
    letr;
    bltr;
    bltr;
    #;
    df2le2;
    cm;
    @121;
    @121;
    @121;
    id;
    #;
    cm;
    tr;
    @121;
    wva1;
    wva0;
    wvd;
    wvb1;
    wve;
    wvb2;
    @71;
    @73;
    @68;
    @71;
    id;
    #;
    @73;
    id;
    #;
    @22;
    @93;
    @67;
    @91;
    wva0;
    wva1;
    orcom;
    wve;
    wvb1;
    orcom;
    2an;
    @136;
    dp34;
    bltr;
    lel2or;
    bltr;
    lelan;
    bltr;
    bltr;
    @103;
    @98;
    @101;
    wo;
    @98;
    @74;
    @68;
    wa;
    #;
    wo;
    #;
    @100;
    @68;
    @97;
    @74;
    mldual;
    @101;
    @139;
    @98;
    @68;
    @74;
    ancom;
    lor;
    @140;
    @98;
    @74;
    wo;
    #;
    @68;
    wa;
    @68;
    @141;
    wa;
    @100;
    @68;
    @74;
    @98;
    @68;
    @97;
    lea;
    ml2i;
    @141;
    @68;
    ancom;
    @141;
    @99;
    @68;
    @98;
    @74;
    ax-a2;
    lan;
    3tr;
    3tr;
    lbtr;
    @100;
    @101;
    @95;
    wo;
    #;
    @96;
    @100;
    @101;
    @98;
    wo;
    @142;
    @68;
    @74;
    @97;
    mldual;
    @98;
    @95;
    @101;
    @98;
    @110;
    @97;
    wa;
    @93;
    @91;
    @97;
    wa;
    #;
    wa;
    #;
    @95;
    @68;
    @110;
    @97;
    @111;
    ran;
    @93;
    @91;
    @97;
    anass;
    @144;
    @93;
    wve;
    @92;
    wo;
    #;
    wa;
    @93;
    wve;
    wa;
    #;
    @92;
    wo;
    #;
    @95;
    @143;
    @145;
    @93;
    @143;
    @91;
    wva1;
    wa;
    #;
    wve;
    wo;
    wve;
    @148;
    wo;
    @145;
    wve;
    wva1;
    @91;
    wve;
    wvb1;
    leor;
    mldual2i;
    @148;
    wve;
    orcom;
    @148;
    @92;
    wve;
    @91;
    wva1;
    ancom;
    lor;
    3tr;
    lan;
    @92;
    wve;
    @93;
    wva1;
    @91;
    wva0;
    leao1;
    mldual2i;
    @147;
    @92;
    @146;
    wo;
    @95;
    @146;
    @92;
    orcom;
    @146;
    @94;
    @92;
    @93;
    wve;
    ancom;
    lor;
    tr;
    3tr;
    3tr;
    lor;
    tr;
    @101;
    @74;
    @95;
    @68;
    @74;
    lear;
    leror;
    bltr;
    letr;
    @96;
    @70;
    @69;
    @94;
    wo;
    #;
    wa;
    #;
    @72;
    @45;
    @92;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    @90;
    @96;
    @74;
    @94;
    @92;
    wo;
    #;
    wo;
    #;
    @70;
    @69;
    wa;
    #;
    @94;
    wo;
    #;
    @73;
    @92;
    wo;
    #;
    wo;
    #;
    @153;
    @95;
    @154;
    @74;
    @92;
    @94;
    orcom;
    lor;
    @155;
    @71;
    @94;
    wo;
    #;
    @158;
    wo;
    @159;
    @71;
    @73;
    @94;
    @92;
    or4;
    @160;
    @157;
    @158;
    @158;
    @71;
    @156;
    @94;
    @71;
    @71;
    @156;
    @137;
    @69;
    @70;
    ancom;
    tr;
    #;
    ror;
    @73;
    @73;
    @92;
    @138;
    ror;
    2or;
    tr;
    @157;
    @150;
    @158;
    @152;
    @70;
    @69;
    @94;
    wve;
    @93;
    wvb2;
    leao1;
    mli;
    @72;
    @45;
    @92;
    wva1;
    @91;
    wvd;
    leao1;
    mli;
    2or;
    3tr;
    @150;
    @86;
    @152;
    @89;
    @149;
    @85;
    @70;
    @149;
    wva0;
    @94;
    wo;
    #;
    wvd;
    wo;
    wva0;
    @84;
    wo;
    #;
    wvd;
    wo;
    @85;
    wva0;
    wvd;
    @94;
    or32;
    @162;
    @163;
    wvd;
    @162;
    wva0;
    wva1;
    wve;
    wva0;
    wo;
    #;
    wa;
    #;
    wo;
    @163;
    wva0;
    wve;
    wva1;
    ml3;
    @165;
    @84;
    wva0;
    @164;
    @83;
    wva1;
    wve;
    wva0;
    orcom;
    lan;
    lor;
    tr;
    ror;
    wva0;
    @84;
    wvd;
    or32;
    3tr;
    lan;
    @151;
    @88;
    @72;
    @151;
    wvb1;
    @92;
    wo;
    #;
    wvb2;
    wo;
    wvb1;
    @87;
    wo;
    #;
    wvb2;
    wo;
    @88;
    wvb1;
    wvb2;
    @92;
    or32;
    @166;
    @167;
    wvb2;
    @166;
    wvb1;
    wva1;
    @67;
    wa;
    #;
    wo;
    @167;
    @92;
    @168;
    wvb1;
    @91;
    @67;
    wva1;
    wvb1;
    wve;
    orcom;
    lan;
    lor;
    wvb1;
    wva1;
    wve;
    ml3;
    tr;
    ror;
    wvb1;
    @87;
    wvb2;
    or32;
    3tr;
    lan;
    2or;
    tr;
    lbtr;
    @86;
    @78;
    @89;
    @81;
    @85;
    @77;
    @70;
    @84;
    @76;
    @69;
    @84;
    wva1;
    @75;
    wva1;
    @83;
    lea;
    @84;
    @113;
    @75;
    wva1;
    @13;
    @83;
    @120;
    leran;
    @135;
    letr;
    ler2an;
    lelor;
    lelan;
    @88;
    @80;
    @72;
    @87;
    @79;
    @45;
    @87;
    wve;
    @75;
    wve;
    @13;
    lea;
    @87;
    @113;
    @75;
    @87;
    @13;
    @83;
    wve;
    @13;
    lear;
    wve;
    @13;
    wva0;
    leao3;
    ler2an;
    @135;
    letr;
    ler2an;
    lelor;
    lelan;
    le2or;
    letr;
    @82;
    @70;
    @69;
    wvb2;
    @72;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @72;
    @45;
    wvd;
    @70;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    @71;
    @169;
    wo;
    #;
    @73;
    @172;
    wo;
    #;
    wo;
    #;
    @74;
    @78;
    @171;
    @81;
    @174;
    @77;
    @170;
    @70;
    wva0;
    wvd;
    @76;
    wo;
    #;
    wo;
    wva0;
    wvd;
    @169;
    wo;
    #;
    wo;
    @77;
    @170;
    @178;
    @179;
    wva0;
    @178;
    wvd;
    wva1;
    wvb2;
    wvd;
    wo;
    #;
    wa;
    #;
    wo;
    @179;
    @76;
    @181;
    wvd;
    @75;
    @180;
    wva1;
    wvd;
    wvb2;
    ax-a2;
    lan;
    lor;
    wvd;
    wva1;
    wvb2;
    ml3;
    tr;
    lor;
    wva0;
    wvd;
    @76;
    orass;
    wva0;
    wvd;
    @169;
    orass;
    3tr1;
    lan;
    @80;
    @173;
    @72;
    wvb1;
    wvb2;
    @79;
    wo;
    #;
    wo;
    wvb1;
    wvb2;
    @172;
    wo;
    #;
    wo;
    @80;
    @173;
    @182;
    @183;
    wvb1;
    wvb2;
    wve;
    wvd;
    ml3;
    lor;
    wvb1;
    wvb2;
    @79;
    orass;
    wvb1;
    wvb2;
    @172;
    orass;
    3tr1;
    lan;
    2or;
    @171;
    @175;
    @174;
    @176;
    @171;
    @156;
    @169;
    wo;
    #;
    @175;
    @169;
    @69;
    @70;
    wvb2;
    @72;
    wve;
    leao3;
    mldual2i;
    @175;
    @184;
    @71;
    @156;
    @169;
    @161;
    ror;
    cm;
    tr;
    @174;
    @176;
    @176;
    @172;
    @45;
    @72;
    wvd;
    @70;
    wva1;
    leao3;
    mldual2i;
    @176;
    @176;
    @73;
    @73;
    @172;
    @138;
    ror;
    cm;
    tr;
    2or;
    @177;
    @74;
    @169;
    @172;
    wo;
    #;
    wo;
    @185;
    @74;
    wo;
    @74;
    @71;
    @169;
    @73;
    @172;
    or4;
    @74;
    @185;
    orcom;
    @185;
    @74;
    @185;
    @73;
    @71;
    wo;
    #;
    @74;
    @169;
    @73;
    @172;
    @71;
    @169;
    @72;
    wvb2;
    wa;
    @73;
    wvb2;
    @72;
    ancom;
    wvb2;
    @45;
    @72;
    wvb2;
    wvb1;
    leor;
    lelan;
    bltr;
    wvd;
    @69;
    @70;
    wvd;
    wva0;
    leor;
    leran;
    le2or;
    @186;
    @186;
    @74;
    @186;
    @186;
    @73;
    @73;
    @71;
    @71;
    @138;
    @137;
    2or;
    cm;
    @73;
    @71;
    orcom;
    tr;
    lbtr;
    df-le2;
    3tr;
    3tr;
    lbtr;
    @67;
    @28;
    @22;
    wve;
    @7;
    wvb1;
    xxdp.e;
    ror;
    lan;
    @71;
    @63;
    @73;
    @65;
    @69;
    @62;
    @70;
    @52;
    wvd;
    @61;
    wva0;
    xxdp.d;
    lor;
    wve;
    @7;
    wvb2;
    xxdp.e;
    ror;
    2an;
    @72;
    @64;
    @45;
    wvd;
    @61;
    wva1;
    xxdp.d;
    lor;
    ran;
    2or;
    le3tr2;
    @63;
    @53;
    @65;
    @59;
    @62;
    @47;
    @52;
    @62;
    wva2;
    wva0;
    @57;
    wo;
    #;
    wo;
    wva2;
    wva0;
    wo;
    @47;
    wva0;
    wva2;
    @57;
    or12;
    @187;
    wva0;
    wva2;
    wva0;
    @13;
    orabs;
    lor;
    wva2;
    wva0;
    orcom;
    3tr;
    ran;
    @59;
    @65;
    @58;
    @64;
    @45;
    wva1;
    wva2;
    @57;
    orass;
    ran;
    cm;
    2or;
    lbtr;
    @59;
    @55;
    @53;
    @58;
    @54;
    @45;
    @58;
    wva2;
    wva1;
    @41;
    wo;
    #;
    wo;
    #;
    @54;
    @58;
    wva2;
    wva1;
    wva0;
    wvb1;
    wva1;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wo;
    #;
    @189;
    @58;
    wva2;
    wva1;
    wo;
    #;
    @191;
    wo;
    @193;
    @44;
    @194;
    @57;
    @191;
    wva1;
    wva2;
    ax-a2;
    @13;
    @190;
    wva0;
    wva1;
    wvb1;
    ax-a2;
    lan;
    2or;
    wva2;
    wva1;
    @191;
    orass;
    tr;
    @192;
    @188;
    wva2;
    wva1;
    wva0;
    wvb1;
    ml3le;
    lelor;
    bltr;
    @189;
    @194;
    @41;
    wo;
    #;
    @54;
    @195;
    @189;
    wva2;
    wva1;
    @41;
    orass;
    cm;
    @194;
    @44;
    @41;
    wva2;
    wva1;
    ax-a2;
    ror;
    tr;
    lbtr;
    leran;
    lelor;
    letr;
    @56;
    @49;
    @46;
    @41;
    wo;
    #;
    wo;
    @51;
    @53;
    @49;
    @55;
    @196;
    @52;
    @48;
    @47;
    @7;
    wvb0;
    wvb2;
    @26;
    leror;
    lelan;
    @55;
    @196;
    @45;
    @54;
    wa;
    @45;
    @44;
    wa;
    #;
    @41;
    wo;
    @55;
    @196;
    @41;
    @44;
    @45;
    wvb1;
    @22;
    wvb2;
    leao1;
    mldual2i;
    @45;
    @54;
    ancom;
    @197;
    @46;
    @41;
    @45;
    @44;
    ancom;
    ror;
    3tr2;
    bile;
    le2or;
    @49;
    @46;
    @41;
    or12;
    lbtr;
    letr;
    @51;
    wvc0;
    wvc1;
    @41;
    wo;
    #;
    wo;
    #;
    @43;
    @199;
    @51;
    wvc0;
    @46;
    @198;
    @50;
    xxdp.c0;
    wvc1;
    @49;
    @41;
    xxdp.c1;
    ror;
    2or;
    cm;
    @43;
    @199;
    wvc0;
    wvc1;
    @41;
    orass;
    cm;
    tr;
    lbtr;
    ler2an;
    @41;
    @0;
    @22;
    wvb1;
    @22;
    lear;
    mldual2i;
    lbtr;
    @41;
    wvb1;
    @23;
    wvb1;
    @22;
    lea;
    lelor;
    letr;
    @23;
    wvb1;
    orcom;
    lbtr;
    @24;
    leid;
    lel2or;
    letr;
    lel2or;
    letr;
    ler2an;
    @21;
    @25;
    @21;
    @3;
    @25;
    @20;
    @2;
    wvb0;
    @20;
    @19;
    @1;
    wo;
    #;
    wvb1;
    wo;
    wvb1;
    @200;
    wo;
    @2;
    @19;
    wvb1;
    @1;
    or32;
    @200;
    wvb1;
    orcom;
    @200;
    @1;
    wvb1;
    @19;
    @1;
    @19;
    wvc2;
    @0;
    @19;
    @22;
    wvb0;
    wvb1;
    wo;
    #;
    wa;
    #;
    wvc2;
    wva0;
    @22;
    wvb0;
    @201;
    wva0;
    wva1;
    leo;
    wvb0;
    wvb1;
    leo;
    le2an;
    wvc2;
    @202;
    xxdp.c2;
    cm;
    lbtr;
    @19;
    wvc1;
    wvc0;
    @19;
    @49;
    wvc1;
    wva0;
    @47;
    wvb0;
    @48;
    wva0;
    wva2;
    leo;
    wvb0;
    wvb2;
    leo;
    le2an;
    wvc1;
    @49;
    xxdp.c1;
    cm;
    lbtr;
    lerr;
    ler2an;
    df-le2;
    lor;
    3tr;
    lan;
    @3;
    wvb0;
    @201;
    @24;
    wa;
    #;
    wa;
    #;
    wvb0;
    @201;
    wa;
    #;
    @24;
    wa;
    #;
    @25;
    @2;
    @203;
    wvb0;
    @2;
    wvb1;
    @23;
    @201;
    wa;
    #;
    wo;
    @24;
    @201;
    wa;
    @203;
    @1;
    @207;
    wvb1;
    @1;
    @202;
    @0;
    wa;
    @207;
    wvc2;
    @202;
    @0;
    xxdp.c2;
    ran;
    @22;
    @201;
    @0;
    an32;
    tr;
    lor;
    @201;
    @23;
    wvb1;
    wvb1;
    wvb0;
    leor;
    ml2i;
    @24;
    @201;
    ancom;
    3tr;
    lan;
    @206;
    @204;
    wvb0;
    @201;
    @24;
    anass;
    cm;
    @205;
    wvb0;
    @24;
    wvb0;
    wvb1;
    anabs;
    ran;
    3tr;
    tr;
    cm;
    lbtr;
    @21;
    @19;
    @3;
    wo;
    #;
    @4;
    @21;
    wvb0;
    @2;
    @19;
    wo;
    #;
    wa;
    @3;
    @19;
    wo;
    @208;
    @20;
    @209;
    wvb0;
    @20;
    @19;
    @2;
    wo;
    @209;
    @19;
    wvb1;
    @1;
    orass;
    @19;
    @2;
    orcom;
    tr;
    lan;
    @19;
    @2;
    wvb0;
    wva0;
    wvb0;
    lear;
    mldual2i;
    @3;
    @19;
    orcom;
    3tr;
    @19;
    wva0;
    @3;
    wva0;
    wvb0;
    lea;
    leror;
    bltr;
    letr;
    df-le2;
    lbtr;
    lel2or;
    letr;
  };

  return $|- p =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) )$;
}
