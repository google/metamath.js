include "kl.mm";
include "kc.mm";
include "tal.mm";
include "hb.mm";
include "wl.mm";
include "ax4g.mm";
include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "cl.mm";
include "a1i.mm";
include "mpbi.mm";

theorem cla4v(hal: $type$ al, vx: $var$ x, ta: $term$ A, tb: $term$ B, tc: $term$ C) {
  assume cla4v.1: $|- A : bool$;
  assume cla4v.2: $|- B : al$;
  assume cla4v.3: $|- [ x : al = B ] |= [ A = C ]$;

  disjoint B x;
  disjoint C x;
  disjoint al x;



  do {
    hal;
    vx;
    ta;
    kl;
    #;
    tb;
    kc;
    #;
    tc;
    tal;
    @0;
    kc;
    #;
    hal;
    tb;
    @0;
    hal;
    hb;
    vx;
    ta;
    cla4v.1;
    wl;
    cla4v.2;
    ax4g;
    #;
    @1;
    tc;
    ke;
    kbr;
    @2;
    @1;
    @2;
    @3;
    ax-cb1;
    hal;
    hb;
    vx;
    ta;
    tc;
    tb;
    cla4v.1;
    cla4v.2;
    cla4v.3;
    cl;
    a1i;
    mpbi;
  };

  return $|- ( ! \ x : al . A ) |= C$;
}
