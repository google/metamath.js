include "wi.mm";
include "wb.mm";
include "biimt.mm";
include "ax-mp.mm";

theorem a1bi(wph: wff ph, wps: wff ps) {
  assume a1bi.1: |- "ph";





  do {
    wph;
    wps;
    wph;
    wps;
    wi;
    wb;
    a1bi.1;
    wph;
    wps;
    biimt;
    ax-mp;
  };

  return |- "( ps <-> ( ph -> ps ) )";
}
