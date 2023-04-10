include "wo.mm";
include "i3ror.mm";
include "i3lor.mm";
include "binr2.mm";

theorem i32or(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume i32or.1: $|- ( a ->3 b ) = 1$;
  assume i32or.2: $|- ( c ->3 d ) = 1$;





  do {
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    wvb;
    wvd;
    wo;
    wva;
    wvb;
    wvc;
    i32or.1;
    i3ror;
    wvc;
    wvd;
    wvb;
    i32or.2;
    i3lor;
    binr2;
  };

  return $|- ( ( a v c ) ->3 ( b v d ) ) = 1$;
}
