include "wex.mm";
include "wi.mm";
include "wn.mm";
include "wal.mm";
include "df-ex.mm";
include "imbi1i.mm";
include "con1b.mm";
include "bitri.mm";

theorem eximal(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {





  do {
    wph;
    vx;
    wex;
    #;
    wps;
    wi;
    wph;
    wn;
    vx;
    wal;
    #;
    wn;
    #;
    wps;
    wi;
    wps;
    wn;
    @1;
    wi;
    @0;
    @2;
    wps;
    wph;
    vx;
    df-ex;
    imbi1i;
    @1;
    wps;
    con1b;
    bitri;
  };

  return '|-' "( ( E. x ph -> ps ) <-> ( -. ps -> A. x -. ph ) )";
}
