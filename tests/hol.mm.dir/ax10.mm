include "kt.mm";
include "tal.mm";
include "tv.mm";
include "ke.mm";
include "kbr.mm";
include "kl.mm";
include "kc.mm";
include "wv.mm";
include "weqi.mm";
include "hb.mm";
include "weq.mm";
include "wov.mm";
include "id.mm";
include "oveq1.mm";
include "cla4v.mm";
include "ax4.mm";
include "eqcomi.mm";
include "eqtri.mm";
include "alrimiv.mm";
include "ht.mm";
include "wal.mm";
include "wl.mm";
include "wc.mm";
include "cbv.mm";
include "ceq2.mm";
include "a1i.mm";
include "mpbir.mm";
include "wtru.mm";
include "adantl.mm";
include "ex.mm";

theorem ax10(hal: $type$ al, vx: $var$ x, vy: $var$ y) {

  disjoint x y;
  disjoint al x;
  disjoint al y;
  disjoint x z;
  disjoint y z;
  disjoint al z;

  let vz: $var$ z;

  do {
    kt;
    tal;
    hal;
    vx;
    hal;
    vx;
    tv;
    #;
    hal;
    vy;
    tv;
    #;
    ke;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    tal;
    hal;
    vy;
    @1;
    @0;
    ke;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    @4;
    kt;
    @7;
    tal;
    hal;
    vz;
    hal;
    vz;
    tv;
    #;
    @0;
    ke;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    @7;
    @4;
    hal;
    vz;
    @9;
    @4;
    hal;
    @8;
    @1;
    @0;
    @4;
    hal;
    vz;
    wv;
    #;
    hal;
    vx;
    @2;
    @8;
    @8;
    @1;
    ke;
    kbr;
    hal;
    @0;
    @1;
    hal;
    vx;
    wv;
    #;
    hal;
    vy;
    wv;
    #;
    weqi;
    #;
    @12;
    hal;
    hal;
    hb;
    @0;
    @1;
    @8;
    ke;
    @0;
    @8;
    ke;
    kbr;
    #;
    hal;
    weq;
    #;
    @13;
    @14;
    @16;
    hal;
    hal;
    hb;
    @0;
    @8;
    ke;
    @17;
    @13;
    @12;
    wov;
    id;
    oveq1;
    cla4v;
    hal;
    @0;
    @1;
    @4;
    @13;
    hal;
    vx;
    @2;
    @15;
    ax4;
    eqcomi;
    eqtri;
    alrimiv;
    @7;
    @11;
    ke;
    kbr;
    @4;
    hal;
    hb;
    ht;
    #;
    hb;
    tal;
    @3;
    hal;
    wal;
    #;
    hal;
    hb;
    vx;
    @2;
    @15;
    wl;
    wc;
    @18;
    hb;
    @6;
    @10;
    tal;
    kt;
    @19;
    hal;
    hb;
    vy;
    @5;
    hal;
    @1;
    @0;
    @14;
    @13;
    weqi;
    #;
    wl;
    hal;
    hb;
    vy;
    vz;
    @5;
    @9;
    @20;
    hal;
    hal;
    hb;
    @1;
    @0;
    @8;
    ke;
    @1;
    @8;
    ke;
    kbr;
    #;
    @17;
    @14;
    @13;
    @21;
    hal;
    @1;
    @8;
    @14;
    @12;
    weqi;
    id;
    oveq1;
    cbv;
    ceq2;
    a1i;
    mpbir;
    wtru;
    adantl;
    ex;
  };

  return $|-$ $T. |= [ ( ! \ x : al . [ x : al = y : al ] ) ==> ( ! \ y : al . [ y : al = x : al ] ) ]$;
}
