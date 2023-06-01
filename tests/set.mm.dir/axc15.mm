include "weq.mm";
include "wal.mm";
include "wn.mm";
include "wex.mm";
include "wi.mm";
include "ax6ev.mm";
include "dveeq2.mm";
include "ax12v.mm";
include "equeuclr.mm";
include "sps.mm";
include "imim1d.mm";
include "al2imi.mm";
include "imim2d.mm";
include "imim12d.mm";
include "syl6mpi.mm";
include "exlimdv.mm";
include "mpi.mm";

theorem axc15(wph: $wff$ ph, vx: $setvar$ x, vy: $setvar$ y) {



  let vz: $setvar$ z;

  do {
    vx;
    vy;
    weq;
    #;
    vx;
    wal;
    wn;
    #;
    vz;
    vy;
    weq;
    #;
    vz;
    wex;
    @0;
    wph;
    @0;
    wph;
    wi;
    #;
    vx;
    wal;
    #;
    wi;
    #;
    wi;
    #;
    vz;
    vy;
    ax6ev;
    @1;
    @2;
    @6;
    vz;
    @1;
    @2;
    @2;
    vx;
    wal;
    #;
    vx;
    vz;
    weq;
    #;
    wph;
    @8;
    wph;
    wi;
    #;
    vx;
    wal;
    #;
    wi;
    #;
    wi;
    @6;
    vx;
    vy;
    vz;
    dveeq2;
    wph;
    vx;
    vz;
    ax12v;
    @7;
    @0;
    @8;
    @11;
    @5;
    @2;
    @0;
    @8;
    wi;
    vx;
    vz;
    vx;
    vy;
    equeuclr;
    #;
    sps;
    @7;
    @10;
    @4;
    wph;
    @2;
    @9;
    @3;
    vx;
    @2;
    @0;
    @8;
    wph;
    @12;
    imim1d;
    al2imi;
    imim2d;
    imim12d;
    syl6mpi;
    exlimdv;
    mpi;
  };

  return $|-$ $( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )$;
}