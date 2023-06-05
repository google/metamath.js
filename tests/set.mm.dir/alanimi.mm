include "wal.mm";
include "ex.mm";
include "al2imi.mm";
include "imp.mm";

theorem alanimi(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume alanimi.1: |- "( ( ph /\\ ps ) -> ch )";





  do {
    wph;
    vx;
    wal;
    wps;
    vx;
    wal;
    wch;
    vx;
    wal;
    wph;
    wps;
    wch;
    vx;
    wph;
    wps;
    wch;
    alanimi.1;
    ex;
    al2imi;
    imp;
  };

  return |- "( ( A. x ph /\\ A. x ps ) -> A. x ch )";
}
