include "wo.mm";
include "wn.mm";
include "wi.mm";
include "df-or.mm";
include "biimpri.mm";

theorem pm2.54(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wo;
    wph;
    wn;
    wps;
    wi;
    wph;
    wps;
    df-or;
    biimpri;
  };

  return $|-$ $( ( -. ph -> ps ) -> ( ph \/ ps ) )$;
}
