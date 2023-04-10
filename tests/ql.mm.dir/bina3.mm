include "wo.mm";
include "leo.mm";
include "lei3.mm";

theorem bina3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    leo;
    lei3;
  };

  return $|- ( a ->3 ( a v b ) ) = 1$;
}
