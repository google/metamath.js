include "wi.mm";
include "wex.mm";
include "wal.mm";
include "19.35.mm";
include "mpbi.mm";

theorem 19.35i(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume 19.35i.1: |- "E. x ( ph -> ps )";





  do {
    wph;
    wps;
    wi;
    vx;
    wex;
    wph;
    vx;
    wal;
    wps;
    vx;
    wex;
    wi;
    19.35i.1;
    wph;
    wps;
    vx;
    19.35;
    mpbi;
  };

  return '|-' "( A. x ph -> E. x ps )";
}
