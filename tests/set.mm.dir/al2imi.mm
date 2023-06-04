include "wi.mm";
include "wal.mm";
include "al2im.mm";
include "mpg.mm";

theorem al2imi(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume al2imi.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    wi;
    wi;
    wph;
    vx;
    wal;
    wps;
    vx;
    wal;
    wch;
    vx;
    wal;
    wi;
    wi;
    vx;
    wph;
    wps;
    wch;
    vx;
    al2im;
    al2imi.1;
    mpg;
  };

  return '|-' "( A. x ph -> ( A. x ps -> A. x ch ) )";
}
