include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "simpl.mm"
include "imim2i.mm"
include "con3.mm"
include "imim2d.mm"
include "syl.mm"
include "anidm.mm"
include "biimpri.mm"
include "jctil.mm"
include "df-nan.mm"
include "anbi2i.mm"
include "notbii.mm"
include "iman.mm"
include "3bitr4i.mm"
include "imnan.mm"
include "bitr4i.mm"
include "con2b.mm"
include "bitr3i.mm"
include "3bitri.mm"
include "xchbinx.mm"
include "anbi12i.mm"
include "mpbir.mm"

theorem nic-axALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) )

  proof
    wph
    wch
    wps
    wnan
    #
    wnan
    #
    wta
    wta
    wta
    wnan
    #
    wnan
    #
    wth
    wch
    wnan
    #
    wph
    wth
    wnan
    #
    @5
    wnan
    #
    wnan
    #
    wnan
    #
    wnan
    @1
    @8
    wa
    #
    wn
    #
    @10
    wph
    wch
    wps
    wa
    #
    wi
    #
    wta
    wta
    wta
    wa
    #
    wi
    #
    wth
    wch
    wn
    #
    wi
    #
    wth
    wph
    wn
    #
    wi
    #
    wi
    #
    wa
    #
    wi
    #
    @12
    @19
    @14
    @12
    wph
    wch
    wi
    #
    @19
    @11
    wch
    wph
    wch
    wps
    simpl
    imim2i
    @22
    @15
    @17
    wth
    wph
    wch
    con3
    imim2d
    syl
    @13
    wta
    wta
    anidm
    biimpri
    jctil
    @10
    @12
    @20
    wn
    #
    wa
    #
    wn
    @21
    @9
    @24
    @1
    @12
    @8
    @23
    wph
    @0
    wa
    #
    wn
    wph
    @11
    wn
    #
    wa
    #
    wn
    @1
    @12
    @25
    @27
    @0
    @26
    wph
    wch
    wps
    df-nan
    anbi2i
    notbii
    wph
    @0
    df-nan
    wph
    @11
    iman
    3bitr4i
    @8
    @3
    @7
    wa
    @20
    @3
    @7
    df-nan
    @3
    @14
    @7
    @19
    wta
    @2
    wa
    #
    wn
    wta
    @13
    wn
    #
    wa
    #
    wn
    @3
    @14
    @28
    @30
    @2
    @29
    wta
    wta
    wta
    df-nan
    anbi2i
    notbii
    wta
    @2
    df-nan
    wta
    @13
    iman
    3bitr4i
    @4
    @6
    wa
    #
    wn
    @16
    @18
    wn
    #
    wa
    #
    wn
    @7
    @19
    @31
    @33
    @4
    @16
    @6
    @32
    @4
    wth
    wch
    wa
    wn
    @16
    wth
    wch
    df-nan
    wth
    wch
    imnan
    bitr4i
    @6
    @5
    @5
    wa
    #
    @18
    @5
    @5
    df-nan
    @34
    @5
    wph
    wth
    wa
    wn
    #
    @18
    @5
    anidm
    wph
    wth
    df-nan
    @35
    wph
    wth
    wn
    wi
    @18
    wph
    wth
    imnan
    wph
    wth
    con2b
    bitr3i
    3bitri
    xchbinx
    anbi12i
    notbii
    @4
    @6
    df-nan
    @16
    @18
    iman
    3bitr4i
    anbi12i
    xchbinx
    anbi12i
    notbii
    @12
    @20
    iman
    bitr4i
    mpbir
    @1
    @8
    df-nan
    mpbir
end
