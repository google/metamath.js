include "wi.mm";
include "ax-1.mm";
include "pm2.27.mm";
include "impbid2.mm";

theorem biimt(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wph;
    wps;
    wi;
    wps;
    wph;
    ax-1;
    wph;
    wps;
    pm2.27;
    impbid2;
  };

  return $|-$ $( ph -> ( ps <-> ( ph -> ps ) ) )$;
}
