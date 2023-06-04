include "wi.mm";
include "pm2.27.mm";
include "syl9.mm";

theorem com23(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume com3.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wi;
    wch;
    wth;
    com3.1;
    wch;
    wth;
    pm2.27;
    syl9;
  };

  return '|-' "( ph -> ( ch -> ( ps -> th ) ) )";
}
