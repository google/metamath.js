include "kt.mm";
include "tal.mm";
include "tex.mm";
include "kl.mm";
include "kc.mm";
include "tv.mm";
include "ke.mm";
include "kbr.mm";
include "tim.mm";
include "hb.mm";
include "ht.mm";
include "tan.mm";
include "wal.mm";
include "wex.mm";
include "wim.mm";
include "wl.mm";
include "wc.mm";
include "wv.mm";
include "weqi.mm";
include "wov.mm";
include "wtru.mm";
include "wan.mm";
include "eqid.mm";
include "alrimiv.mm";
include "a1i.mm";
include "ax-cb1.mm";
include "weq.mm";
include "id.mm";
include "ceq1.mm";
include "beta.mm";
include "eqtri.mm";
include "oveq1.mm";
include "ax-17.mm";
include "ax-hbl1.mm";
include "hbov.mm";
include "leqf.mm";
include "ceq2.mm";
include "hbl1.mm";
include "hbc.mm";
include "hbl.mm";
include "clf.mm";
include "mpbir.mm";
include "ax4e.mm";
include "syl.mm";
include "adantl.mm";
include "ex.mm";

theorem axrep(hal: $type$ al, hbe: $type$ be, vx: $var$ x, vy: $var$ y, vz: $var$ z, ta: $term$ A, tb: $term$ B) {
  assume axrep.1: $|- A : bool$;
  assume axrep.2: $|- B : ( al -> bool )$;

  disjoint B y;
  disjoint al y;
  disjoint x y;
  disjoint be x;
  disjoint be y;
  disjoint y z;
  disjoint be z;
  disjoint A f;
  disjoint f y;
  disjoint B f;
  disjoint al f;
  disjoint f x;
  disjoint be f;
  disjoint f z;

  let vf: $var$ f;
  let hga: $type$ ga;

  do {
    kt;
    tal;
    hal;
    vx;
    tex;
    hbe;
    vy;
    tal;
    hbe;
    vz;
    tal;
    hbe;
    vy;
    ta;
    kl;
    #;
    kc;
    #;
    hbe;
    vz;
    tv;
    #;
    hbe;
    vy;
    tv;
    #;
    ke;
    kbr;
    #;
    tim;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    kl;
    #;
    kc;
    #;
    kl;
    #;
    kc;
    #;
    tex;
    hbe;
    hb;
    ht;
    #;
    vy;
    tal;
    hbe;
    vz;
    @12;
    vy;
    tv;
    #;
    @2;
    kc;
    #;
    tex;
    hal;
    vx;
    tb;
    hal;
    vx;
    tv;
    #;
    kc;
    #;
    @1;
    tan;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    ke;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    kl;
    #;
    kc;
    #;
    @11;
    kt;
    @24;
    @11;
    @23;
    hbe;
    vz;
    @19;
    kl;
    #;
    kc;
    #;
    @24;
    tal;
    hbe;
    vz;
    @19;
    @19;
    ke;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    @26;
    @11;
    @29;
    @11;
    hal;
    hb;
    ht;
    #;
    hb;
    tal;
    @10;
    hal;
    wal;
    hal;
    hb;
    vx;
    @9;
    @12;
    hb;
    tex;
    @8;
    hbe;
    wex;
    #;
    hbe;
    hb;
    vy;
    @7;
    @12;
    hb;
    tal;
    @6;
    hbe;
    wal;
    #;
    hbe;
    hb;
    vz;
    @5;
    hb;
    hb;
    hb;
    @1;
    @4;
    tim;
    wim;
    @12;
    hb;
    tal;
    @0;
    @32;
    hbe;
    hb;
    vy;
    ta;
    axrep.1;
    wl;
    #;
    wc;
    #;
    hbe;
    @2;
    @3;
    hbe;
    vz;
    wv;
    #;
    hbe;
    vy;
    wv;
    weqi;
    wov;
    wl;
    wc;
    wl;
    wc;
    wl;
    wc;
    hbe;
    vz;
    @27;
    kt;
    hb;
    @19;
    kt;
    wtru;
    @30;
    hb;
    tex;
    @18;
    hal;
    wex;
    #;
    hal;
    hb;
    vx;
    @17;
    hb;
    hb;
    hb;
    @16;
    @1;
    tan;
    wan;
    hal;
    hb;
    tb;
    @15;
    axrep.2;
    hal;
    vx;
    wv;
    wc;
    #;
    @34;
    wov;
    #;
    wl;
    #;
    wc;
    #;
    eqid;
    alrimiv;
    a1i;
    #;
    @26;
    @29;
    ke;
    kbr;
    @11;
    @29;
    @11;
    @41;
    ax-cb1;
    @12;
    hb;
    vy;
    vf;
    @22;
    @29;
    @25;
    @12;
    hb;
    tal;
    @21;
    @32;
    hbe;
    hb;
    vz;
    @20;
    hb;
    @14;
    @19;
    hbe;
    hb;
    @13;
    @2;
    @12;
    vy;
    wv;
    #;
    @35;
    wc;
    #;
    @40;
    weqi;
    #;
    wl;
    #;
    wc;
    #;
    hbe;
    hb;
    vz;
    @19;
    @40;
    wl;
    #;
    @12;
    hb;
    @21;
    @28;
    tal;
    @13;
    @25;
    ke;
    kbr;
    #;
    @32;
    @45;
    hbe;
    hb;
    vz;
    vf;
    @20;
    @27;
    @48;
    @44;
    hb;
    hb;
    hb;
    @14;
    @19;
    @19;
    ke;
    @48;
    hb;
    weq;
    #;
    @43;
    @40;
    hb;
    @14;
    @25;
    @2;
    kc;
    #;
    @19;
    @48;
    @43;
    hbe;
    hb;
    @2;
    @13;
    @48;
    @25;
    @42;
    @35;
    @48;
    @12;
    @13;
    @25;
    @42;
    @47;
    weqi;
    #;
    id;
    ceq1;
    @50;
    @19;
    ke;
    kbr;
    @48;
    @51;
    hbe;
    hb;
    vz;
    @19;
    @40;
    beta;
    a1i;
    eqtri;
    oveq1;
    hbe;
    @12;
    @12;
    hb;
    vz;
    @13;
    hbe;
    vf;
    tv;
    #;
    @25;
    ke;
    kt;
    @12;
    weq;
    @42;
    hbe;
    vf;
    wv;
    #;
    @47;
    hbe;
    hb;
    hb;
    hb;
    ht;
    ht;
    #;
    vz;
    ke;
    @52;
    @49;
    @53;
    ax-17;
    hbe;
    @12;
    vz;
    @13;
    @52;
    @42;
    @53;
    ax-17;
    hbe;
    hbe;
    hb;
    vz;
    @19;
    @52;
    @40;
    @53;
    ax-hbl1;
    hbov;
    leqf;
    ceq2;
    @12;
    @12;
    hb;
    vy;
    @28;
    @12;
    vf;
    tv;
    #;
    tal;
    kt;
    @32;
    hbe;
    hb;
    vz;
    @27;
    hb;
    @19;
    @19;
    @40;
    @40;
    weqi;
    #;
    wl;
    @12;
    vf;
    wv;
    #;
    @12;
    @12;
    hb;
    ht;
    #;
    vy;
    tal;
    @55;
    @32;
    @57;
    ax-17;
    #;
    @12;
    hbe;
    hb;
    vy;
    vz;
    @27;
    @55;
    kt;
    @56;
    @57;
    @12;
    hb;
    hb;
    hb;
    vy;
    @19;
    @55;
    @19;
    ke;
    kt;
    @49;
    @40;
    @57;
    @40;
    @12;
    hga;
    hga;
    hb;
    ht;
    ht;
    vy;
    ke;
    @55;
    hga;
    weq;
    @57;
    ax-17;
    @12;
    @30;
    hb;
    vy;
    @18;
    @55;
    tex;
    kt;
    @36;
    @39;
    @57;
    @12;
    @58;
    vy;
    tex;
    @55;
    @31;
    @57;
    ax-17;
    @12;
    hal;
    hb;
    vy;
    vx;
    @17;
    @55;
    kt;
    @38;
    @57;
    @12;
    hb;
    hb;
    hb;
    vy;
    @16;
    @55;
    @1;
    tan;
    kt;
    wan;
    @37;
    @57;
    @34;
    @12;
    @54;
    vy;
    tan;
    @55;
    wan;
    @57;
    ax-17;
    @12;
    hb;
    vy;
    @16;
    @55;
    @37;
    @57;
    ax-17;
    @12;
    @12;
    hb;
    vy;
    @0;
    @55;
    tal;
    kt;
    @32;
    @33;
    @57;
    @59;
    @12;
    hbe;
    hb;
    vy;
    ta;
    @55;
    kt;
    axrep.1;
    @57;
    wtru;
    hbl1;
    hbc;
    hbov;
    hbl;
    hbc;
    #;
    @60;
    hbov;
    hbl;
    hbc;
    @12;
    hbe;
    hb;
    vy;
    vz;
    @19;
    @55;
    kt;
    @40;
    @57;
    @60;
    hbl;
    clf;
    a1i;
    mpbir;
    @12;
    @25;
    @23;
    @12;
    hb;
    vy;
    @22;
    @46;
    wl;
    @47;
    ax4e;
    syl;
    wtru;
    adantl;
    ex;
  };

  return $|-$ $T. |= [ ( ! \ x : al . ( ? \ y : be . ( ! \ z : be . [ ( ! \ y : be . A ) ==> [ z : be = y : be ] ] ) ) ) ==> ( ? \ y : ( be -> bool ) . ( ! \ z : be . [ ( y : ( be -> bool ) z : be ) = ( ? \ x : al . [ ( B x : al ) /\ ( ! \ y : be . A ) ] ) ] ) ) ]$;
}
