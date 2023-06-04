include "wal.mm";
include "wex.mm";
include "wn.mm";
include "con3d.mm";
include "al2imi.mm";
include "alnex.mm";
include "3imtr3g.mm";
include "con4d.mm";

theorem aleximi(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume aleximi.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    vx;
    wal;
    #;
    wch;
    vx;
    wex;
    #;
    wps;
    vx;
    wex;
    #;
    @0;
    wch;
    wn;
    #;
    vx;
    wal;
    wps;
    wn;
    #;
    vx;
    wal;
    @1;
    wn;
    @2;
    wn;
    wph;
    @3;
    @4;
    vx;
    wph;
    wps;
    wch;
    aleximi.1;
    con3d;
    al2imi;
    wch;
    vx;
    alnex;
    wps;
    vx;
    alnex;
    3imtr3g;
    con4d;
  };

  return '|-' "( A. x ph -> ( E. x ps -> E. x ch ) )";
}
