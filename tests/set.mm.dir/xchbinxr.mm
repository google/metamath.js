include "bicomi.mm";
include "xchbinx.mm";

theorem xchbinxr(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume xchbinxr.1: |- "( ph <-> -. ps )";
  assume xchbinxr.2: |- "( ch <-> ps )";





  do {
    wph;
    wps;
    wch;
    xchbinxr.1;
    wch;
    wps;
    xchbinxr.2;
    bicomi;
    xchbinx;
  };

  return '|-' "( ph <-> -. ch )";
}
