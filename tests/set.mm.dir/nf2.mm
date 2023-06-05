include "wnf.mm";
include "wex.mm";
include "wal.mm";
include "wi.mm";
include "wn.mm";
include "wo.mm";
include "df-nf.mm";
include "imor.mm";
include "orcom.mm";
include "3bitri.mm";

theorem nf2(wph: wff ph, vx: setvar x) {





  do {
    wph;
    vx;
    wnf;
    wph;
    vx;
    wex;
    #;
    wph;
    vx;
    wal;
    #;
    wi;
    @0;
    wn;
    #;
    @1;
    wo;
    @1;
    @2;
    wo;
    wph;
    vx;
    df-nf;
    @0;
    @1;
    imor;
    @2;
    @1;
    orcom;
    3bitri;
  };

  return |- "( F/ x ph <-> ( A. x ph \\/ -. E. x ph ) )";
}
