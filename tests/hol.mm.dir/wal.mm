include "hb.mm";
include "ht.mm";
include "tv.mm";
include "kt.mm";
include "kl.mm";
include "ke.mm";
include "kbr.mm";
include "tal.mm";
include "wv.mm";
include "wtru.mm";
include "wl.mm";
include "weqi.mm";
include "df-al.mm";
include "eqtypri.mm";

theorem wal(hal: type al) {



  let vf: var f;
  let vp: var p;
  let vq: var q;
  let vx: var x;
  let vy: var y;

  do {
    hal;
    hb;
    ht;
    #;
    hb;
    ht;
    @0;
    vp;
    @0;
    vp;
    tv;
    #;
    hal;
    vx;
    kt;
    kl;
    #;
    ke;
    kbr;
    #;
    kl;
    tal;
    kt;
    @0;
    hb;
    vp;
    @3;
    @0;
    @1;
    @2;
    @0;
    vp;
    wv;
    hal;
    hb;
    vx;
    kt;
    wtru;
    wl;
    weqi;
    wl;
    hal;
    vx;
    vp;
    df-al;
    eqtypri;
  };

  return |- "! : ( ( al -> bool ) -> bool )";
}
