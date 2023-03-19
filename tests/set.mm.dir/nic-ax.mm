include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "nannan.mm"
include "biimpi.mm"
include "simpl.mm"
include "imim2i.mm"
include "wn.mm"
include "imnan.mm"
include "df-nan.mm"
include "bitr4i.mm"
include "con3.mm"
include "imim2d.mm"
include "con2b.mm"
include "3bitr4ri.mm"
include "syl6ibr.mm"
include "syl5bir.mm"
include "nanim.mm"
include "sylib.mm"
include "3syl.mm"
include "pm4.24.mm"
include "mpbir.mm"
include "jctil.mm"

theorem nic-ax
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
    wnan
    #
    wta
    wta
    wta
    wnan
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
    @3
    wnan
    wnan
    #
    wnan
    wnan
    @0
    @1
    @4
    wa
    wi
    @0
    @4
    @1
    @0
    wph
    wch
    wps
    wa
    #
    wi
    #
    wph
    wch
    wi
    #
    @4
    @0
    @6
    wph
    wps
    wch
    nannan
    biimpi
    @5
    wch
    wph
    wch
    wps
    simpl
    imim2i
    @7
    @2
    @3
    wi
    @4
    @2
    wth
    wch
    wn
    #
    wi
    #
    @7
    @3
    @9
    wth
    wch
    wa
    wn
    @2
    wth
    wch
    imnan
    wth
    wch
    df-nan
    bitr4i
    @7
    @9
    wth
    wph
    wn
    #
    wi
    #
    @3
    @7
    @8
    @10
    wth
    wph
    wch
    con3
    imim2d
    wph
    wth
    wn
    wi
    wph
    wth
    wa
    wn
    @11
    @3
    wph
    wth
    imnan
    wth
    wph
    con2b
    wph
    wth
    df-nan
    3bitr4ri
    syl6ibr
    syl5bir
    @2
    @3
    nanim
    sylib
    3syl
    @1
    wta
    wta
    wta
    wa
    #
    wi
    wta
    @12
    wta
    pm4.24
    biimpi
    wta
    wta
    wta
    nannan
    mpbir
    jctil
    @0
    @4
    @1
    nannan
    mpbir
end
