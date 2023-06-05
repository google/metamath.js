include "wal.mm";
include "wex.mm";
include "biimpd.mm";
include "aleximi.mm";
include "biimprd.mm";
include "impbid.mm";

theorem alexbii(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume alexbii.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    vx;
    wal;
    wps;
    vx;
    wex;
    wch;
    vx;
    wex;
    wph;
    wps;
    wch;
    vx;
    wph;
    wps;
    wch;
    alexbii.1;
    biimpd;
    aleximi;
    wph;
    wch;
    wps;
    vx;
    wph;
    wps;
    wch;
    alexbii.1;
    biimprd;
    aleximi;
    impbid;
  };

  return |- "( A. x ph -> ( E. x ps <-> E. x ch ) )";
}
