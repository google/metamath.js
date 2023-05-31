include "wn.mm";
include "a1d.mm";
include "con4d.mm";

theorem pm2.21d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume pm2.21d.1: $|- ( ph -> -. ps )$;





  do {
    wph;
    wch;
    wps;
    wph;
    wps;
    wn;
    wch;
    wn;
    pm2.21d.1;
    a1d;
    con4d;
  };

  return $|-$ $( ph -> ( ps -> ch ) )$;
}
