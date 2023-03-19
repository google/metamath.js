include "wb.mm"
include "wnan.mm"
include "bicom1.mm"
include "nanbi2.mm"
include "nanbi12d.mm"
include "wa.mm"
include "wi.mm"
include "nannan.mm"
include "simpr.mm"
include "imim2i.mm"
include "sylbi.mm"
include "impbid21d.mm"
include "wn.mm"
include "wo.mm"
include "notbii.mm"
include "pm4.61.mm"
include "ianor.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "pm5.1.mm"
include "ancoms.mm"
include "ad2ant2r.mm"
include "syl2anb.mm"
include "ex.mm"
include "bija.mm"
include "impbii.mm"
include "nancom.mm"
include "nanbi2i.mm"
include "bitri.mm"
include "bibi1i.mm"

theorem rp-fakenanass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ch ) <-> ( ( ( ph -/\ ps ) -/\ ch ) <-> ( ph -/\ ( ps -/\ ch ) ) ) )

  proof
    wph
    wch
    wb
    #
    wch
    wps
    wph
    wnan
    #
    wnan
    #
    wph
    wps
    wch
    wnan
    #
    wnan
    #
    wb
    #
    wph
    wps
    wnan
    #
    wch
    wnan
    #
    @4
    wb
    @0
    @5
    @0
    wch
    wph
    @1
    @3
    wph
    wch
    bicom1
    wph
    wch
    wps
    nanbi2
    nanbi12d
    @2
    @4
    @0
    @2
    @4
    wph
    wch
    @4
    wph
    wps
    wch
    wa
    #
    wi
    #
    wph
    wch
    wi
    wph
    wch
    wps
    nannan
    #
    @8
    wch
    wph
    wps
    wch
    simpr
    imim2i
    sylbi
    @2
    wch
    wps
    wph
    wa
    #
    wi
    #
    wch
    wph
    wi
    wch
    wph
    wps
    nannan
    #
    @11
    wph
    wch
    wps
    wph
    simpr
    imim2i
    sylbi
    impbid21d
    @2
    wn
    #
    @4
    wn
    #
    @0
    @14
    wch
    wps
    wn
    #
    wph
    wn
    wo
    #
    wa
    #
    wph
    @16
    wch
    wn
    wo
    #
    wa
    #
    @0
    @15
    @14
    @12
    wn
    wch
    @11
    wn
    #
    wa
    @18
    @2
    @12
    @13
    notbii
    wch
    @11
    pm4.61
    @21
    @17
    wch
    wps
    wph
    ianor
    anbi2i
    3bitri
    @15
    @9
    wn
    wph
    @8
    wn
    #
    wa
    @20
    @4
    @9
    @10
    notbii
    wph
    @8
    pm4.61
    @22
    @19
    wph
    wps
    wch
    ianor
    anbi2i
    3bitri
    wch
    wph
    @0
    @17
    @19
    wph
    wch
    @0
    wph
    wch
    pm5.1
    ancoms
    ad2ant2r
    syl2anb
    ex
    bija
    impbii
    @2
    @7
    @4
    @2
    wch
    @6
    wnan
    @7
    @1
    @6
    wch
    wps
    wph
    nancom
    nanbi2i
    wch
    @6
    nancom
    bitri
    bibi1i
    bitri
end
