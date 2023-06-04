include "ax-5.mm";
include "exbidh.mm";

theorem exbidv(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
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
    exbidh;
  };

  return '|-' "( ph -> ( E. x ps <-> E. x ch ) )";
}
