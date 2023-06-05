include "wa.mm";
include "wal.mm";
include "simpl.mm";
include "alimi.mm";
include "simpr.mm";
include "jca.mm";
include "id.mm";
include "alanimi.mm";
include "impbii.mm";

theorem 19.26(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wa;
    #;
    vx;
    wal;
    #;
    wph;
    vx;
    wal;
    #;
    wps;
    vx;
    wal;
    #;
    wa;
    @1;
    @2;
    @3;
    @0;
    wph;
    vx;
    wph;
    wps;
    simpl;
    alimi;
    @0;
    wps;
    vx;
    wph;
    wps;
    simpr;
    alimi;
    jca;
    wph;
    wps;
    @0;
    vx;
    @0;
    id;
    alanimi;
    impbii;
  };

  return |- "( A. x ( ph /\\ ps ) <-> ( A. x ph /\\ A. x ps ) )";
}
