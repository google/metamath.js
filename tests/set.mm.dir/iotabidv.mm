include "wb.mm";
include "wal.mm";
include "cio.mm";
include "wceq.mm";
include "alrimiv.mm";
include "iotabi.mm";
include "syl.mm";

theorem iotabidv(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume iotabidv.1: |- "( ph -> ( ps <-> ch ) )";

  disjoint ph x;



  do {
    wph;
    wps;
    wch;
    wb;
    #;
    vx;
    wal;
    wps;
    vx;
    cio;
    wch;
    vx;
    cio;
    wceq;
    wph;
    @0;
    vx;
    iotabidv.1;
    alrimiv;
    wps;
    wch;
    vx;
    iotabi;
    syl;
  };

  return |- "( ph -> ( iota x ps ) = ( iota x ch ) )";
}
