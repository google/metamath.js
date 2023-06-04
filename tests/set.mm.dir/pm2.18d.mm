include "wn.mm";
include "wi.mm";
include "pm2.18.mm";
include "syl.mm";

theorem pm2.18d(wph: 'wff' ph, wps: 'wff' ps) {
  assume pm2.18d.1: |- "( ph -> ( -. ps -> ps ) )";





  do {
    wph;
    wps;
    wn;
    wps;
    wi;
    wps;
    pm2.18d.1;
    wps;
    pm2.18;
    syl;
  };

  return '|-' "( ph -> ps )";
}
