include "wn.mm"
include "wi.mm"
include "wnan.mm"
include "wa.mm"
include "w3nand.mm"
include "iman.mm"
include "imnan.mm"
include "biimpi.mm"
include "jca.mm"
include "biimpri.mm"
include "adantl.mm"
include "impbii.mm"
include "df-nan.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "anbi2i.mm"
include "notbii.mm"
include "3bitr4i.mm"
include "df-3nand.mm"

theorem df3nandALT1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -/\ ps -/\ ch ) <-> ( ph -/\ ( ( ps -/\ ch ) -/\ ( ps -/\ ch ) ) ) )

  proof
    wph
    wps
    wch
    wn
    wi
    #
    wi
    #
    wph
    wps
    wch
    wnan
    #
    @2
    wnan
    #
    wa
    #
    wn
    #
    wph
    wps
    wch
    w3nand
    wph
    @3
    wnan
    wph
    @2
    @2
    wa
    #
    wi
    wph
    @6
    wn
    #
    wa
    #
    wn
    @1
    @5
    wph
    @6
    iman
    @0
    @6
    wph
    @0
    wps
    wch
    wa
    wn
    #
    @9
    wa
    #
    @6
    @0
    @10
    @0
    @9
    @9
    @0
    @9
    wps
    wch
    imnan
    #
    biimpi
    #
    @12
    jca
    @9
    @0
    @9
    @0
    @9
    @11
    biimpri
    adantl
    impbii
    @2
    @9
    @2
    @9
    wps
    wch
    df-nan
    #
    @13
    anbi12i
    bitr4i
    imbi2i
    @4
    @8
    @3
    @7
    wph
    @2
    @2
    df-nan
    anbi2i
    notbii
    3bitr4i
    wph
    wps
    wch
    df-3nand
    wph
    @3
    df-nan
    3bitr4i
end
