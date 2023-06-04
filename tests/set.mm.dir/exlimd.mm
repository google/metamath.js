include "wex.mm";
include "eximd.mm";
include "19.9.mm";
include "syl6ib.mm";

theorem exlimd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume exlimd.1: |- "F/ x ph";
  assume exlimd.2: |- "F/ x ch";
  assume exlimd.3: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    vx;
    wex;
    wch;
    vx;
    wex;
    wch;
    wph;
    wps;
    wch;
    vx;
    exlimd.1;
    exlimd.3;
    eximd;
    wch;
    vx;
    exlimd.2;
    19.9;
    syl6ib;
  };

  return '|-' "( ph -> ( E. x ps -> ch ) )";
}
