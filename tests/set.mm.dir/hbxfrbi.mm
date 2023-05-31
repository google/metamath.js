include "wal.mm";
include "albii.mm";
include "3imtr4i.mm";

theorem hbxfrbi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume hbxfrbi.1: $|- ( ph <-> ps )$;
  assume hbxfrbi.2: $|- ( ps -> A. x ps )$;





  do {
    wps;
    wps;
    vx;
    wal;
    wph;
    wph;
    vx;
    wal;
    hbxfrbi.2;
    hbxfrbi.1;
    wph;
    wps;
    vx;
    hbxfrbi.1;
    albii;
    3imtr4i;
  };

  return $|-$ $( ph -> A. x ph )$;
}
