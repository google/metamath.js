include "wn.mm";
include "wi.mm";
include "a1i.mm";
include "pm2.61d.mm";

theorem pm2.61d1(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume pm2.61d1.1: $|- ( ph -> ( ps -> ch ) )$;
  assume pm2.61d1.2: $|- ( -. ps -> ch )$;





  do {
    wph;
    wps;
    wch;
    pm2.61d1.1;
    wps;
    wn;
    wch;
    wi;
    wph;
    pm2.61d1.2;
    a1i;
    pm2.61d;
  };

  return $|-$ $( ph -> ch )$;
}
