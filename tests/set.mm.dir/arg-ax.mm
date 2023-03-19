include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "wn.mm"
include "df-nan.mm"
include "wo.mm"
include "pm4.57.mm"
include "orel2.mm"
include "com12.mm"
include "simpr.mm"
include "a1i.mm"
include "jad.mm"
include "pm3.45.mm"
include "anim12i.mm"
include "jaob.mm"
include "3imtr4i.mm"
include "syl.mm"
include "pm3.22.mm"
include "syl6.mm"
include "syl5bi.mm"
include "con1d.mm"
include "biimpri.mm"
include "nannan.mm"
include "ancli.mm"
include "mpbir.mm"

theorem arg-ax
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ch -/\ th ) -/\ ( ph -/\ th ) ) ) ) )

  proof
    wph
    wps
    wch
    wnan
    wnan
    #
    @0
    wth
    wch
    wnan
    #
    wch
    wth
    wnan
    #
    wph
    wth
    wnan
    #
    wnan
    wnan
    #
    wnan
    wnan
    @0
    @0
    @4
    wa
    wi
    @0
    @4
    wph
    wps
    wch
    wa
    #
    wi
    #
    @1
    @2
    @3
    wa
    #
    wi
    @0
    @4
    @1
    wth
    wch
    wa
    #
    wn
    #
    @6
    @7
    wth
    wch
    df-nan
    @6
    @9
    wch
    wth
    wa
    #
    wn
    #
    wph
    wth
    wa
    #
    wn
    #
    wa
    #
    @7
    @6
    @14
    @8
    @14
    wn
    @10
    @12
    wo
    #
    @6
    @8
    @10
    @12
    pm4.57
    @6
    @15
    @10
    @8
    @6
    wch
    wph
    wo
    #
    wch
    wi
    #
    @15
    @10
    wi
    #
    @16
    @6
    wch
    @16
    wph
    @5
    wch
    wph
    wn
    @16
    wch
    wph
    wch
    orel2
    com12
    @5
    wch
    wi
    @16
    wps
    wch
    simpr
    a1i
    jad
    com12
    wch
    wch
    wi
    #
    wph
    wch
    wi
    #
    wa
    @10
    @10
    wi
    #
    @12
    @10
    wi
    #
    wa
    @17
    @18
    @19
    @21
    @20
    @22
    wch
    wch
    wth
    pm3.45
    wph
    wch
    wth
    pm3.45
    anim12i
    wch
    wch
    wph
    jaob
    @10
    @10
    @12
    jaob
    3imtr4i
    syl
    wch
    wth
    pm3.22
    syl6
    syl5bi
    con1d
    @11
    @2
    @13
    @3
    @2
    @11
    wch
    wth
    df-nan
    biimpri
    @3
    @13
    wph
    wth
    df-nan
    biimpri
    anim12i
    syl6
    syl5bi
    wph
    wch
    wps
    nannan
    @1
    @3
    @2
    nannan
    3imtr4i
    ancli
    @0
    @4
    @0
    nannan
    mpbir
end
