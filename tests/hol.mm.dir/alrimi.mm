include "kl.mm";
include "kt.mm";
include "ke.mm";
include "kbr.mm";
include "tal.mm";
include "kc.mm";
include "hb.mm";
include "ax-cb2.mm";
include "wtru.mm";
include "eqtru.mm";
include "eqcomi.mm";
include "leqf.mm";
include "ax-cb1.mm";
include "wl.mm";
include "alval.mm";
include "a1i.mm";
include "mpbir.mm";

theorem alrimi(hal: $type$ al, vx: $var$ x, vy: $var$ y, ta: $term$ A, tr: $term$ R) {
  assume alrimi.1: $|- R |= A$;
  assume alrimi.2: $|- T. |= [ ( \ x : al . R y : al ) = R ]$;

  disjoint A y;
  disjoint R y;
  disjoint x y;
  disjoint al x;
  disjoint al y;



  do {
    hal;
    vx;
    ta;
    kl;
    #;
    hal;
    vx;
    kt;
    kl;
    ke;
    kbr;
    #;
    tal;
    @0;
    kc;
    #;
    tr;
    hal;
    hb;
    vx;
    vy;
    ta;
    kt;
    tr;
    ta;
    tr;
    alrimi.1;
    ax-cb2;
    #;
    hb;
    kt;
    ta;
    tr;
    wtru;
    ta;
    tr;
    alrimi.1;
    eqtru;
    eqcomi;
    alrimi.2;
    leqf;
    @2;
    @1;
    ke;
    kbr;
    tr;
    ta;
    tr;
    alrimi.1;
    ax-cb1;
    hal;
    vx;
    @0;
    hal;
    hb;
    vx;
    ta;
    @3;
    wl;
    alval;
    a1i;
    mpbir;
  };

  return $|-$ $R |= ( ! \ x : al . A )$;
}
