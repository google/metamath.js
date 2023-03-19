include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"

theorem 3an4anass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) <-> ( ( ph /\ ps ) /\ ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    wph
    wps
    wa
    #
    wch
    wa
    #
    wth
    wa
    @1
    wch
    wth
    wa
    wa
    @0
    @2
    wth
    wph
    wps
    wch
    df-3an
    anbi1i
    @1
    wch
    wth
    anass
    bitri
end
