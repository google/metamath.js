include "wif.mm"
include "wb.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "dfifp4.mm"
include "bibi2i.mm"
include "dfbi2.mm"
include "imor.mm"
include "ordi.mm"
include "ancomst.mm"
include "impexp.mm"
include "imbi2i.mm"
include "bitri.mm"
include "3bitrri.mm"
include "bicomi.mm"
include "anbi12i.mm"
include "3bitri.mm"
include "df-or.mm"
include "cases2.mm"
include "imbi1i.mm"
include "jaob.mm"
include "pm5.6.mm"
include "anbi2i.mm"
include "ancom.mm"
include "an4.mm"

theorem ifpidg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( th <-> if- ( ph , ps , ch ) ) <-> ( ( ( ( ph /\ ps ) -> th ) /\ ( ( ph /\ th ) -> ps ) ) /\ ( ( ch -> ( ph \/ th ) ) /\ ( th -> ( ph \/ ch ) ) ) ) )

  proof
    wth
    wph
    wps
    wch
    wif
    #
    wb
    wth
    wph
    wn
    #
    wps
    wo
    #
    wph
    wch
    wo
    #
    wa
    #
    wb
    #
    wph
    wth
    wa
    wps
    wi
    #
    wth
    @3
    wi
    #
    wa
    #
    wph
    wps
    wa
    #
    wth
    wi
    #
    wch
    wph
    wth
    wo
    wi
    #
    wa
    #
    wa
    #
    @10
    @6
    wa
    @11
    @7
    wa
    wa
    #
    @0
    @4
    wth
    wph
    wps
    wch
    dfifp4
    bibi2i
    @5
    wth
    @4
    wi
    #
    @4
    wth
    wi
    #
    wa
    @13
    wth
    @4
    dfbi2
    @15
    @8
    @16
    @12
    @15
    wth
    wn
    #
    @4
    wo
    @17
    @2
    wo
    #
    @17
    @3
    wo
    #
    wa
    @8
    wth
    @4
    imor
    @17
    @2
    @3
    ordi
    @18
    @6
    @19
    @7
    @6
    wth
    wph
    wa
    wps
    wi
    wth
    wph
    wps
    wi
    #
    wi
    #
    @18
    wph
    wth
    wps
    ancomst
    wth
    wph
    wps
    impexp
    @21
    wth
    @2
    wi
    @18
    @20
    @2
    wth
    wph
    wps
    imor
    #
    imbi2i
    wth
    @2
    imor
    bitri
    3bitrri
    @7
    @19
    wth
    @3
    imor
    bicomi
    anbi12i
    3bitri
    @16
    @9
    @1
    wch
    wa
    #
    wo
    #
    wth
    wi
    @10
    @23
    wth
    wi
    #
    wa
    @12
    @4
    @24
    wth
    @4
    @20
    @1
    wch
    wi
    #
    wa
    #
    @24
    @2
    @20
    @3
    @26
    @20
    @2
    @22
    bicomi
    wph
    wch
    df-or
    anbi12i
    @24
    @27
    wph
    wps
    wch
    cases2
    bicomi
    bitri
    imbi1i
    @9
    wth
    @23
    jaob
    @25
    @11
    @10
    @25
    wch
    @1
    wa
    wth
    wi
    @11
    @1
    wch
    wth
    ancomst
    wch
    wph
    wth
    pm5.6
    bitri
    anbi2i
    3bitri
    anbi12i
    bitri
    @13
    @12
    @8
    wa
    @14
    @8
    @12
    ancom
    @10
    @11
    @6
    @7
    an4
    bitri
    3bitri
end
