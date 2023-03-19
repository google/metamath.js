include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "anandi.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "bitr4i.mm"

theorem an3andi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) ) <-> ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    w3a
    #
    wa
    #
    wph
    wps
    wa
    #
    wph
    wch
    wa
    #
    wa
    #
    wph
    wth
    wa
    #
    wa
    #
    @2
    @3
    @5
    w3a
    @1
    wph
    wps
    wch
    wa
    #
    wth
    wa
    #
    wa
    wph
    @7
    wa
    #
    @5
    wa
    @6
    @0
    @8
    wph
    wps
    wch
    wth
    df-3an
    anbi2i
    wph
    @7
    wth
    anandi
    @9
    @4
    @5
    wph
    wps
    wch
    anandi
    anbi1i
    3bitri
    @2
    @3
    @5
    df-3an
    bitr4i
end
