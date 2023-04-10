include "wo.mm";
include "ax-a3.mm";
include "bi1.mm";

theorem wa3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wo;
    wvc;
    wo;
    wva;
    wvb;
    wvc;
    wo;
    wo;
    wva;
    wvb;
    wvc;
    ax-a3;
    bi1;
  };

  return $|- ( ( ( a v b ) v c ) == ( a v ( b v c ) ) ) = 1$;
}
