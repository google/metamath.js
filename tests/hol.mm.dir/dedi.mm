include "kt.mm";
include "wtru.mm";
include "adantl.mm";
include "ded.mm";

theorem dedi(ts: $term$ S, tt: $term$ T) {
  assume dedi.1: $|- S |= T$;
  assume dedi.2: $|- T |= S$;





  do {
    kt;
    ts;
    tt;
    ts;
    kt;
    tt;
    dedi.1;
    wtru;
    adantl;
    tt;
    kt;
    ts;
    dedi.2;
    wtru;
    adantl;
    ded;
  };

  return $|- T. |= [ S = T ]$;
}
