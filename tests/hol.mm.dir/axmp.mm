include "kt.mm";
include "mpd.mm";

theorem axmp(tr: $term$ R, ts: $term$ S) {
  assume axmp.1: $|- S : bool$;
  assume axmp.2: $|- T. |= R$;
  assume axmp.3: $|- T. |= [ R ==> S ]$;





  do {
    kt;
    tr;
    ts;
    axmp.1;
    axmp.2;
    axmp.3;
    mpd;
  };

  return $|-$ $T. |= S$;
}
