include "wn.mm";
include "notbii.mm";
include "bitri.mm";

theorem xchbinx(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume xchbinx.1: |- "( ph <-> -. ps )";
  assume xchbinx.2: |- "( ps <-> ch )";





  do {
    wph;
    wps;
    wn;
    wch;
    wn;
    xchbinx.1;
    wps;
    wch;
    xchbinx.2;
    notbii;
    bitri;
  };

  return '|-' "( ph <-> -. ch )";
}
