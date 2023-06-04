include "ax-5.mm";
include "alrimdh.mm";

theorem alrimdv(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume alrimdv.1: |- "( ph -> ( ps -> ch ) )";

  disjoint ph x;
  disjoint ps x;



  do {
    wph;
    wps;
    wch;
    vx;
    wph;
    vx;
    ax-5;
    wps;
    vx;
    ax-5;
    alrimdv.1;
    alrimdh;
  };

  return '|-' "( ph -> ( ps -> A. x ch ) )";
}
