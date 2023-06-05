include "wb.mm";
include "wnf.mm";
include "nfbiit.mm";
include "mpg.mm";

theorem nfbii(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume nfbii.1: |- "( ph <-> ps )";





  do {
    wph;
    wps;
    wb;
    wph;
    vx;
    wnf;
    wps;
    vx;
    wnf;
    wb;
    vx;
    wph;
    wps;
    vx;
    nfbiit;
    nfbii.1;
    mpg;
  };

  return |- "( F/ x ph <-> F/ x ps )";
}
