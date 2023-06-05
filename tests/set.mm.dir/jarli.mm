include "wn.mm";
include "wi.mm";
include "pm2.21.mm";
include "syl.mm";

theorem jarli(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume jarli.1: |- "( ( ph -> ps ) -> ch )";





  do {
    wph;
    wn;
    wph;
    wps;
    wi;
    wch;
    wph;
    wps;
    pm2.21;
    jarli.1;
    syl;
  };

  return |- "( -. ph -> ch )";
}
