include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "3anass.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"

theorem bnj250
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ( ( ps /\ ch ) /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    wph
    wps
    wch
    wa
    #
    wa
    #
    wth
    wa
    wph
    @1
    wth
    wa
    wa
    wph
    wps
    wch
    wth
    df-bnj17
    @0
    @2
    wth
    wph
    wps
    wch
    3anass
    anbi1i
    wph
    @1
    wth
    anass
    3bitri
end
