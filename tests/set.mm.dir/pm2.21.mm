include "wn.mm";
include "id.mm";
include "pm2.21d.mm";

theorem pm2.21(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wn;
    #;
    wph;
    wps;
    @0;
    id;
    pm2.21d;
  };

  return '|-' "( -. ph -> ( ph -> ps ) )";
}
