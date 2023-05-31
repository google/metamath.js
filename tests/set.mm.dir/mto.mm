include "wn.mm";
include "a1i.mm";
include "pm2.65i.mm";

theorem mto(wph: $wff$ ph, wps: $wff$ ps) {
  assume mto.1: $|- -. ps$;
  assume mto.2: $|- ( ph -> ps )$;





  do {
    wph;
    wps;
    mto.2;
    wps;
    wn;
    wph;
    mto.1;
    a1i;
    pm2.65i;
  };

  return $|-$ $-. ph$;
}
