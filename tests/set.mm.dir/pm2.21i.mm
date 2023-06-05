include "wn.mm";
include "a1i.mm";
include "con4i.mm";

theorem pm2.21i(wph: wff ph, wps: wff ps) {
  assume pm2.21i.1: |- "-. ph";





  do {
    wps;
    wph;
    wph;
    wn;
    wps;
    wn;
    pm2.21i.1;
    a1i;
    con4i;
  };

  return |- "( ph -> ps )";
}
