include "wn.mm";
include "wi.mm";
include "wo.mm";
include "pm2.54.mm";
include "syl.mm";

theorem orrd(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume orrd.1: |- "( ph -> ( -. ps -> ch ) )";





  do {
    wph;
    wps;
    wn;
    wch;
    wi;
    wps;
    wch;
    wo;
    orrd.1;
    wps;
    wch;
    pm2.54;
    syl;
  };

  return |- "( ph -> ( ps \\/ ch ) )";
}
