include "wn.mm";
include "notnotr.mm";
include "syl5.mm";
include "con4d.mm";

theorem con2d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume con2d.1: |- "( ph -> ( ps -> -. ch ) )";





  do {
    wph;
    wps;
    wn;
    #;
    wch;
    @0;
    wn;
    wps;
    wph;
    wch;
    wn;
    wps;
    notnotr;
    con2d.1;
    syl5;
    con4d;
  };

  return '|-' "( ph -> ( ch -> -. ps ) )";
}
