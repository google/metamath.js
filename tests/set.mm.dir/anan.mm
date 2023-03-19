include "wa.mm"
include "an4.mm"
include "anandi.mm"
include "ancom.mm"
include "bitr3i.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"

theorem anan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ( ( ph /\ th ) /\ ta ) ) <-> ( ( ps /\ th ) /\ ( ph /\ ( ch /\ ta ) ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    wph
    wth
    wa
    #
    wta
    wa
    wa
    @0
    @1
    wa
    #
    wch
    wta
    wa
    #
    wa
    wps
    wth
    wa
    #
    wph
    wa
    #
    @3
    wa
    @4
    wph
    @3
    wa
    wa
    @0
    wch
    @1
    wta
    an4
    @2
    @5
    @3
    @2
    wph
    @4
    wa
    @5
    wph
    wps
    wth
    anandi
    wph
    @4
    ancom
    bitr3i
    anbi1i
    @4
    wph
    @3
    anass
    3bitri
end
