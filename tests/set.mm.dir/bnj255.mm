include "w-bnj17.mm"
include "wa.mm"
include "w3a.mm"
include "bnj251.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem bnj255
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ps /\ ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    wth
    wa
    #
    wa
    wa
    wph
    wps
    @0
    w3a
    wph
    wps
    wch
    wth
    bnj251
    wph
    wps
    @0
    3anass
    bitr4i
end
