include "wn.mm";
include "wi.mm";
include "pm2.27.mm";
include "con2d.mm";

theorem pm3.2im(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wph;
    wps;
    wn;
    #;
    wi;
    wps;
    wph;
    @0;
    pm2.27;
    con2d;
  };

  return |- "( ph -> ( ps -> -. ( ph -> -. ps ) ) )";
}
