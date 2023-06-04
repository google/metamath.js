include "nf5ri.mm";
include "alimdh.mm";

theorem alimd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume alimd.1: |- "F/ x ph";
  assume alimd.2: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    vx;
    wph;
    vx;
    alimd.1;
    nf5ri;
    alimd.2;
    alimdh;
  };

  return '|-' "( ph -> ( A. x ps -> A. x ch ) )";
}
