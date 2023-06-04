include "expdcom.mm";
include "com3r.mm";

theorem expd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume expd.1: |- "( ph -> ( ( ps /\\ ch ) -> th ) )";





  do {
    wps;
    wch;
    wph;
    wth;
    wph;
    wps;
    wch;
    wth;
    expd.1;
    expdcom;
    com3r;
  };

  return '|-' "( ph -> ( ps -> ( ch -> th ) ) )";
}
