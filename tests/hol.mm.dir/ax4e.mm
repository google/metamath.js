include "tal.mm";
include "hb.mm";
include "tv.mm";
include "kc.mm";
include "tim.mm";
include "kbr.mm";
include "kl.mm";
include "tex.mm";
include "kct.mm";
include "wv.mm";
include "wc.mm";
include "ht.mm";
include "wal.mm";
include "wim.mm";
include "wov.mm";
include "wl.mm";
include "simpl.mm";
include "ke.mm";
include "weqi.mm";
include "id.mm";
include "ceq2.mm";
include "oveq1.mm";
include "cla4v.mm";
include "adantl.mm";
include "mpd.mm";
include "ex.mm";
include "alrimiv.mm";
include "exval.mm";
include "a1i.mm";
include "mpbir.mm";

theorem ax4e(hal: $type$ al, ta: $term$ A, tf: $term$ F) {
  assume ax4e.1: $|- F : ( al -> bool )$;
  assume ax4e.2: $|- A : al$;



  let vp: $var$ p;
  let vx: $var$ x;

  do {
    tal;
    hb;
    vp;
    tal;
    hal;
    vx;
    tf;
    hal;
    vx;
    tv;
    #;
    kc;
    #;
    hb;
    vp;
    tv;
    #;
    tim;
    kbr;
    #;
    kl;
    #;
    kc;
    #;
    @2;
    tim;
    kbr;
    #;
    kl;
    kc;
    #;
    tex;
    tf;
    kc;
    #;
    tf;
    ta;
    kc;
    #;
    hb;
    vp;
    @6;
    @9;
    @9;
    @5;
    @2;
    @9;
    @5;
    kct;
    @9;
    @2;
    hb;
    vp;
    wv;
    #;
    @9;
    @5;
    hal;
    hb;
    tf;
    ta;
    ax4e.1;
    ax4e.2;
    wc;
    #;
    hal;
    hb;
    ht;
    hb;
    tal;
    @4;
    hal;
    wal;
    hal;
    hb;
    vx;
    @3;
    hb;
    hb;
    hb;
    @1;
    @2;
    tim;
    wim;
    hal;
    hb;
    tf;
    @0;
    ax4e.1;
    hal;
    vx;
    wv;
    #;
    wc;
    #;
    @10;
    wov;
    #;
    wl;
    wc;
    simpl;
    @5;
    @9;
    @9;
    @2;
    tim;
    kbr;
    #;
    hal;
    vx;
    @3;
    ta;
    @15;
    @14;
    ax4e.2;
    hb;
    hb;
    hb;
    @1;
    @2;
    @9;
    tim;
    @0;
    ta;
    ke;
    kbr;
    #;
    wim;
    @13;
    @10;
    hal;
    hb;
    @0;
    ta;
    tf;
    @16;
    ax4e.1;
    @12;
    @16;
    hal;
    @0;
    ta;
    @12;
    ax4e.2;
    weqi;
    id;
    ceq2;
    oveq1;
    cla4v;
    @11;
    adantl;
    mpd;
    ex;
    alrimiv;
    @8;
    @7;
    ke;
    kbr;
    @9;
    @11;
    hal;
    vx;
    vp;
    tf;
    ax4e.1;
    exval;
    a1i;
    mpbir;
  };

  return $|-$ $( F A ) |= ( ? F )$;
}