include "wnf.mm";
include "nfbii.mm";
include "sylibr.mm";

theorem nfxfrd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume nfbii.1: |- "( ph <-> ps )";
  assume nfxfrd.2: |- "( ch -> F/ x ps )";





  do {
    wch;
    wps;
    vx;
    wnf;
    wph;
    vx;
    wnf;
    nfxfrd.2;
    wph;
    wps;
    vx;
    nfbii.1;
    nfbii;
    sylibr;
  };

  return '|-' "( ch -> F/ x ph )";
}
