include "wal.mm";
include "ax-gen.mm";
include "mpbi.mm";

theorem mpgbi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume mpgbi.1: $|- ( A. x ph <-> ps )$;
  assume mpgbi.2: $|- ph$;





  do {
    wph;
    vx;
    wal;
    wps;
    wph;
    vx;
    mpgbi.2;
    ax-gen;
    mpgbi.1;
    mpbi;
  };

  return $|-$ $ps$;
}
