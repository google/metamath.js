include "eqcomi.mm";
include "eqtypi.mm";
include "3eqtr4i.mm";

theorem 3eqtr3i(hal: $type$ al, ta: $term$ A, tb: $term$ B, tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume 3eqtr4i.1: $|- A : al$;
  assume 3eqtr4i.2: $|- R |= [ A = B ]$;
  assume 3eqtr3i.3: $|- R |= [ A = S ]$;
  assume 3eqtr3i.4: $|- R |= [ B = T ]$;





  do {
    hal;
    ta;
    tb;
    tr;
    ts;
    tt;
    3eqtr4i.1;
    3eqtr4i.2;
    hal;
    ta;
    ts;
    tr;
    3eqtr4i.1;
    3eqtr3i.3;
    eqcomi;
    hal;
    tb;
    tt;
    tr;
    hal;
    ta;
    tb;
    tr;
    3eqtr4i.1;
    3eqtr4i.2;
    eqtypi;
    3eqtr3i.4;
    eqcomi;
    3eqtr4i;
  };

  return $|-$ $R |= [ S = T ]$;
}
