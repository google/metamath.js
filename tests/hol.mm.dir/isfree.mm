include "kt.mm";
include "tal.mm";
include "kl.mm";
include "kc.mm";
include "id.mm";
include "alrimi.mm";
include "tv.mm";
include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "adantl.mm";
include "ex.mm";

theorem isfree(hal: $type$ al, vx: $var$ x, vy: $var$ y, ta: $term$ A) {
  assume alnex1.1: $|- A : bool$;
  assume isfree.2: $|- T. |= [ ( \ x : al . A y : al ) = A ]$;

  disjoint A y;
  disjoint x y;
  disjoint al x;
  disjoint al y;



  do {
    kt;
    ta;
    tal;
    hal;
    vx;
    ta;
    kl;
    #;
    kc;
    #;
    ta;
    kt;
    @1;
    hal;
    vx;
    vy;
    ta;
    ta;
    ta;
    alnex1.1;
    id;
    isfree.2;
    alrimi;
    @0;
    hal;
    vy;
    tv;
    kc;
    ta;
    ke;
    kbr;
    kt;
    isfree.2;
    ax-cb1;
    adantl;
    ex;
  };

  return $|-$ $T. |= [ A ==> ( ! \ x : al . A ) ]$;
}
