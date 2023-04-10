include "kl.mm";
include "tv.mm";
include "kc.mm";
include "tal.mm";
include "hb.mm";
include "wl.mm";
include "wv.mm";
include "ax4g.mm";
include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "beta.mm";
include "a1i.mm";
include "mpbi.mm";

theorem ax4(hal: $type$ al, vx: $var$ x, ta: $term$ A) {
  assume ax4.1: $|- A : bool$;





  do {
    hal;
    vx;
    ta;
    kl;
    #;
    hal;
    vx;
    tv;
    #;
    kc;
    #;
    ta;
    tal;
    @0;
    kc;
    #;
    hal;
    @1;
    @0;
    hal;
    hb;
    vx;
    ta;
    ax4.1;
    wl;
    hal;
    vx;
    wv;
    ax4g;
    #;
    @2;
    ta;
    ke;
    kbr;
    @3;
    @2;
    @3;
    @4;
    ax-cb1;
    hal;
    hb;
    vx;
    ta;
    ax4.1;
    beta;
    a1i;
    mpbi;
  };

  return $|-$ $( ! \ x : al . A ) |= A$;
}
