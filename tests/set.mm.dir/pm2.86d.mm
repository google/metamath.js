include "wi.mm";
include "ax-1.mm";
include "syl5.mm";
include "com23.mm";

theorem pm2.86d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume pm2.86d.1: $|- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) )$;





  do {
    wph;
    wch;
    wps;
    wth;
    wch;
    wps;
    wch;
    wi;
    wph;
    wps;
    wth;
    wi;
    wch;
    wps;
    ax-1;
    pm2.86d.1;
    syl5;
    com23;
  };

  return $|-$ $( ph -> ( ps -> ( ch -> th ) ) )$;
}
