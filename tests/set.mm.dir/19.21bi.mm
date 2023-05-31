include "wal.mm";
include "sp.mm";
include "syl.mm";

theorem 19.21bi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume 19.21bi.1: $|- ( ph -> A. x ps )$;





  do {
    wph;
    wps;
    vx;
    wal;
    wps;
    19.21bi.1;
    wps;
    vx;
    sp;
    syl;
  };

  return $|-$ $( ph -> ps )$;
}
