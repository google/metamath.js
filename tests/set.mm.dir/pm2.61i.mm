include "wi.mm";
include "id.mm";
include "ja.mm";
include "ax-mp.mm";

theorem pm2.61i(wph: 'wff' ph, wps: 'wff' ps) {
  assume pm2.61i.1: |- "( ph -> ps )";
  assume pm2.61i.2: |- "( -. ph -> ps )";





  do {
    wph;
    wph;
    wi;
    wps;
    wph;
    id;
    wph;
    wph;
    wps;
    pm2.61i.2;
    pm2.61i.1;
    ja;
    ax-mp;
  };

  return '|-' "ps";
}
