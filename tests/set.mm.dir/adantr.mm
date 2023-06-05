include "a1d.mm";
include "imp.mm";

theorem adantr(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume adantr.1: |- "( ph -> ps )";





  do {
    wph;
    wch;
    wps;
    wph;
    wps;
    wch;
    adantr.1;
    a1d;
    imp;
  };

  return |- "( ( ph /\\ ch ) -> ps )";
}
