include "wn.mm";
include "pm2.21.mm";
include "com12.mm";

theorem pm2.24(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wn;
    wph;
    wps;
    wph;
    wps;
    pm2.21;
    com12;
  };

  return $|-$ $( ph -> ( -. ph -> ps ) )$;
}
