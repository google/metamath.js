include "wa.mm";
include "wi.mm";
include "wb.mm";
include "simpl.mm";
include "biantru.mm";
include "anclb.mm";
include "dfbi2.mm";
include "3bitr4i.mm";

theorem pm4.71(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wph;
    wps;
    wa;
    #;
    wi;
    #;
    @1;
    @0;
    wph;
    wi;
    #;
    wa;
    wph;
    wps;
    wi;
    wph;
    @0;
    wb;
    @2;
    @1;
    wph;
    wps;
    simpl;
    biantru;
    wph;
    wps;
    anclb;
    wph;
    @0;
    dfbi2;
    3bitr4i;
  };

  return $|-$ $( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) )$;
}
