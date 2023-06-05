include "wex.mm";
include "wn.mm";
include "wal.mm";
include "df-ex.mm";
include "nfnd.mm";
include "nfald.mm";
include "nfxfrd.mm";

theorem nfexd(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {
  assume nfald.1: |- "F/ y ph";
  assume nfald.2: |- "( ph -> F/ x ps )";





  do {
    wps;
    vy;
    wex;
    wps;
    wn;
    #;
    vy;
    wal;
    #;
    wn;
    wph;
    vx;
    wps;
    vy;
    df-ex;
    wph;
    @1;
    vx;
    wph;
    @0;
    vx;
    vy;
    nfald.1;
    wph;
    wps;
    vx;
    nfald.2;
    nfnd;
    nfald;
    nfnd;
    nfxfrd;
  };

  return |- "( ph -> F/ x E. y ps )";
}
