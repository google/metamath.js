include "wn.mm";
include "wi.mm";
include "con4.mm";
include "syl.mm";

theorem con4d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume con4d.1: |- "( ph -> ( -. ps -> -. ch ) )";





  do {
    wph;
    wps;
    wn;
    wch;
    wn;
    wi;
    wch;
    wps;
    wi;
    con4d.1;
    wps;
    wch;
    con4;
    syl;
  };

  return '|-' "( ph -> ( ch -> ps ) )";
}
