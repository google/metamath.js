include "wi.mm";
include "com23.mm";
include "com12.mm";

theorem com3r(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume com3.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";





  do {
    wph;
    wch;
    wps;
    wth;
    wi;
    wph;
    wps;
    wch;
    wth;
    com3.1;
    com23;
    com12;
  };

  return '|-' "( ch -> ( ph -> ( ps -> th ) ) )";
}
