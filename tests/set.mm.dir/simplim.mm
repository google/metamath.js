include "wi.mm";
include "pm2.21.mm";
include "con1i.mm";

theorem simplim(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wph;
    wps;
    wi;
    wph;
    wps;
    pm2.21;
    con1i;
  };

  return |- "( -. ( ph -> ps ) -> ph )";
}
