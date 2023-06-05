include "wal.mm";
include "alimi.mm";
include "syl.mm";

theorem sylg(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume sylg.1: |- "( ph -> A. x ps )";
  assume sylg.2: |- "( ps -> ch )";





  do {
    wph;
    wps;
    vx;
    wal;
    wch;
    vx;
    wal;
    sylg.1;
    wps;
    wch;
    vx;
    sylg.2;
    alimi;
    syl;
  };

  return |- "( ph -> A. x ch )";
}
