include "ax-5.mm";
include "albidh.mm";

theorem albidv(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume albidv.1: |- "( ph -> ( ps <-> ch ) )";

  disjoint ph x;



  do {
    wph;
    wps;
    wch;
    vx;
    wph;
    vx;
    ax-5;
    albidv.1;
    albidh;
  };

  return |- "( ph -> ( A. x ps <-> A. x ch ) )";
}
