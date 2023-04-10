include "wa.mm";
include "i3ran.mm";
include "i3lan.mm";
include "binr2.mm";

theorem i32an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume i32an.1: $|- ( a ->3 b ) = 1$;
  assume i32an.2: $|- ( c ->3 d ) = 1$;





  do {
    wva;
    wvc;
    wa;
    wvb;
    wvc;
    wa;
    wvb;
    wvd;
    wa;
    wva;
    wvb;
    wvc;
    i32an.1;
    i3ran;
    wvc;
    wvd;
    wvb;
    i32an.2;
    i3lan;
    binr2;
  };

  return $|-$ $( ( a ^ c ) ->3 ( b ^ d ) ) = 1$;
}
