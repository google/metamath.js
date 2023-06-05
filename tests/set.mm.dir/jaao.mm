include "wa.mm";
include "wi.mm";
include "adantr.mm";
include "adantl.mm";
include "jaod.mm";

theorem jaao(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume jaao.1: |- "( ph -> ( ps -> ch ) )";
  assume jaao.2: |- "( th -> ( ta -> ch ) )";





  do {
    wph;
    wth;
    wa;
    wps;
    wch;
    wta;
    wph;
    wps;
    wch;
    wi;
    wth;
    jaao.1;
    adantr;
    wth;
    wta;
    wch;
    wi;
    wph;
    jaao.2;
    adantl;
    jaod;
  };

  return |- "( ( ph /\\ th ) -> ( ( ps \\/ ta ) -> ch ) )";
}
