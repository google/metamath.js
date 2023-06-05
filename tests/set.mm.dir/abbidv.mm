include "sbbidv.mm";
include "abbilem.mm";

theorem abbidv(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume abbidv.1: |- "( ph -> ( ps <-> ch ) )";

  disjoint ph x;
  disjoint x y;
  disjoint ph y;
  disjoint ps y;
  disjoint ch y;

  let vy: setvar y;

  do {
    wph;
    wps;
    wch;
    vx;
    vy;
    wph;
    wps;
    wch;
    vx;
    vy;
    abbidv.1;
    sbbidv;
    abbilem;
  };

  return |- "( ph -> { x | ps } = { x | ch } )";
}
