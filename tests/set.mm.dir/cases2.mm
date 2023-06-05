include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi.mm";
include "pm4.83.mm";
include "dedlema.mm";
include "pm5.74i.mm";
include "dedlemb.mm";
include "anbi12i.mm";
include "ancom.mm";
include "orbi12i.mm";
include "3bitr4ri.mm";

theorem cases2(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wph;
    wps;
    wph;
    wa;
    #;
    wch;
    wph;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wi;
    #;
    @1;
    @3;
    wi;
    #;
    wa;
    @3;
    wph;
    wps;
    wi;
    #;
    @1;
    wch;
    wi;
    #;
    wa;
    wph;
    wps;
    wa;
    #;
    @1;
    wch;
    wa;
    #;
    wo;
    wph;
    @3;
    pm4.83;
    @6;
    @4;
    @7;
    @5;
    wph;
    wps;
    @3;
    wph;
    wps;
    wch;
    dedlema;
    pm5.74i;
    @1;
    wch;
    @3;
    wph;
    wps;
    wch;
    dedlemb;
    pm5.74i;
    anbi12i;
    @8;
    @0;
    @9;
    @2;
    wph;
    wps;
    ancom;
    @1;
    wch;
    ancom;
    orbi12i;
    3bitr4ri;
  };

  return |- "( ( ( ph /\\ ps ) \\/ ( -. ph /\\ ch ) ) <-> ( ( ph -> ps ) /\\ ( -. ph -> ch ) ) )";
}
