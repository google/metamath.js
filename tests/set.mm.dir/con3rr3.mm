include "wn.mm";
include "con3d.mm";
include "com12.mm";

theorem con3rr3(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume con3rr3.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wch;
    wn;
    wps;
    wn;
    wph;
    wps;
    wch;
    con3rr3.1;
    con3d;
    com12;
  };

  return '|-' "( -. ch -> ( ph -> -. ps ) )";
}
