include "ax-5.mm";
include "alimdh.mm";

theorem alimdv(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume alimdv.1: |- "( ph -> ( ps -> ch ) )";

  disjoint ph x;



  do {
    wph;
    wps;
    wch;
    vx;
    wph;
    vx;
    ax-5;
    alimdv.1;
    alimdh;
  };

  return |- "( ph -> ( A. x ps -> A. x ch ) )";
}
