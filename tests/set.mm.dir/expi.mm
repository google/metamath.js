include "wn.mm";
include "wi.mm";
include "pm3.2im.mm";
include "syl6.mm";

theorem expi(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume expi.1: |- "( -. ( ph -> -. ps ) -> ch )";





  do {
    wph;
    wps;
    wph;
    wps;
    wn;
    wi;
    wn;
    wch;
    wph;
    wps;
    pm3.2im;
    expi.1;
    syl6;
  };

  return |- "( ph -> ( ps -> ch ) )";
}
