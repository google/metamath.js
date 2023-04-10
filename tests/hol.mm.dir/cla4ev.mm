include "kl.mm";
include "kc.mm";
include "tex.mm";
include "hb.mm";
include "tv.mm";
include "ke.mm";
include "kbr.mm";
include "eqtypi.mm";
include "id.mm";
include "cl.mm";
include "a1i.mm";
include "mpbir.mm";
include "wl.mm";
include "ax4e.mm";
include "syl.mm";

theorem cla4ev(hal: $type$ al, vx: $var$ x, ta: $term$ A, tb: $term$ B, tc: $term$ C) {
  assume cla4ev.1: $|- A : bool$;
  assume cla4ev.2: $|- B : al$;
  assume cla4ev.3: $|- [ x : al = B ] |= [ A = C ]$;

  disjoint B x;
  disjoint C x;
  disjoint al x;



  do {
    tc;
    hal;
    vx;
    ta;
    kl;
    #;
    tb;
    kc;
    #;
    tex;
    @0;
    kc;
    tc;
    @1;
    tc;
    tc;
    hb;
    ta;
    tc;
    hal;
    vx;
    tv;
    tb;
    ke;
    kbr;
    cla4ev.1;
    cla4ev.3;
    eqtypi;
    #;
    id;
    @1;
    tc;
    ke;
    kbr;
    tc;
    @2;
    hal;
    hb;
    vx;
    ta;
    tc;
    tb;
    cla4ev.1;
    cla4ev.2;
    cla4ev.3;
    cl;
    a1i;
    mpbir;
    hal;
    tb;
    @0;
    hal;
    hb;
    vx;
    ta;
    cla4ev.1;
    wl;
    cla4ev.2;
    ax4e;
    syl;
  };

  return $|-$ $C |= ( ? \ x : al . A )$;
}
