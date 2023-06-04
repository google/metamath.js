include "wnf.mm";
include "wex.mm";
include "wal.mm";
include "wi.mm";
include "19.38b.mm";
include "19.3t.mm";
include "imbi2d.mm";
include "bitr3d.mm";

theorem 19.23t(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {





  do {
    wps;
    vx;
    wnf;
    #;
    wph;
    vx;
    wex;
    #;
    wps;
    vx;
    wal;
    #;
    wi;
    wph;
    wps;
    wi;
    vx;
    wal;
    @1;
    wps;
    wi;
    wph;
    wps;
    vx;
    19.38b;
    @0;
    @2;
    wps;
    @1;
    wps;
    vx;
    19.3t;
    imbi2d;
    bitr3d;
  };

  return '|-' "( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) )";
}
