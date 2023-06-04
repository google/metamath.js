include "id.mm";
include "mpd.mm";

theorem pm2.43i(wph: 'wff' ph, wps: 'wff' ps) {
  assume pm2.43i.1: |- "( ph -> ( ph -> ps ) )";





  do {
    wph;
    wph;
    wps;
    wph;
    id;
    pm2.43i.1;
    mpd;
  };

  return '|-' "( ph -> ps )";
}
