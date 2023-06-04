include "wex.mm";
include "wal.mm";
include "nfrd.mm";
include "sp.mm";
include "syl6.mm";

theorem 19.9d(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume 19.9d.1: |- "( ps -> F/ x ph )";





  do {
    wps;
    wph;
    vx;
    wex;
    wph;
    vx;
    wal;
    wph;
    wps;
    wph;
    vx;
    19.9d.1;
    nfrd;
    wph;
    vx;
    sp;
    syl6;
  };

  return '|-' "( ps -> ( E. x ph -> ph ) )";
}
