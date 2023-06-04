include "wnf.mm";
include "wi.mm";
include "nfimt.mm";
include "mp2an.mm";

theorem nfim(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume nfim.1: |- "F/ x ph";
  assume nfim.2: |- "F/ x ps";





  do {
    wph;
    vx;
    wnf;
    wps;
    vx;
    wnf;
    wph;
    wps;
    wi;
    vx;
    wnf;
    nfim.1;
    nfim.2;
    wph;
    wps;
    vx;
    nfimt;
    mp2an;
  };

  return '|-' "F/ x ( ph -> ps )";
}
