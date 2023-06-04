include "wnf.mm";
include "wex.mm";
include "wal.mm";
include "wi.mm";
include "df-nf.mm";
include "sylib.mm";

theorem nfrd(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume nfrd.1: |- "( ph -> F/ x ps )";





  do {
    wph;
    wps;
    vx;
    wnf;
    wps;
    vx;
    wex;
    wps;
    vx;
    wal;
    wi;
    nfrd.1;
    wps;
    vx;
    df-nf;
    sylib;
  };

  return '|-' "( ph -> ( E. x ps -> A. x ps ) )";
}
