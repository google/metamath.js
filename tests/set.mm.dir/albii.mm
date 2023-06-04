include "wb.mm";
include "wal.mm";
include "albi.mm";
include "mpg.mm";

theorem albii(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume albii.1: |- "( ph <-> ps )";





  do {
    wph;
    wps;
    wb;
    wph;
    vx;
    wal;
    wps;
    vx;
    wal;
    wb;
    vx;
    wph;
    wps;
    vx;
    albi;
    albii.1;
    mpg;
  };

  return '|-' "( A. x ph <-> A. x ps )";
}
