include "wo.mm";
include "wn.mm";
include "wi.mm";
include "df-or.mm";
include "biimpi.mm";

theorem pm2.53(wph: wff ph, wps: wff ps) {





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
    biimpi;
  };

  return |- "( ( ph \\/ ps ) -> ( -. ph -> ps ) )";
}
