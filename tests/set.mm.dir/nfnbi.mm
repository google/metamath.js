include "wal.mm";
include "wn.mm";
include "wo.mm";
include "wnf.mm";
include "orcom.mm";
include "nf3.mm";
include "notnotb.mm";
include "albii.mm";
include "orbi2i.mm";
include "bitr4i.mm";
include "3bitr4i.mm";

theorem nfnbi(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wal;
    #;
    wph;
    wn;
    #;
    vx;
    wal;
    #;
    wo;
    @2;
    @0;
    wo;
    #;
    wph;
    vx;
    wnf;
    @1;
    vx;
    wnf;
    #;
    @0;
    @2;
    orcom;
    wph;
    vx;
    nf3;
    @4;
    @2;
    @1;
    wn;
    #;
    vx;
    wal;
    #;
    wo;
    @3;
    @1;
    vx;
    nf3;
    @0;
    @6;
    @2;
    wph;
    @5;
    vx;
    wph;
    notnotb;
    albii;
    orbi2i;
    bitr4i;
    3bitr4i;
  };

  return $|-$ $( F/ x ph <-> F/ x -. ph )$;
}
