include "hb.mm";
include "ke.mm";
include "weq.mm";
include "wov.mm";

theorem weqi(hal: $type$ al, ta: $term$ A, tb: $term$ B) {
  assume weqi.1: $|- A : al$;
  assume weqi.2: $|- B : al$;





  do {
    hal;
    hal;
    hb;
    ta;
    tb;
    ke;
    hal;
    weq;
    weqi.1;
    weqi.2;
    wov;
  };

  return $|-$ $[ A = B ] : bool$;
}
