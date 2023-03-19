include "w-bnj17.mm"
include "wa.mm"
include "bnj248.mm"
include "anass.mm"
include "bitri.mm"

theorem bnj256
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ph /\ ps ) /\ ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wa
    #
    wch
    wa
    wth
    wa
    @0
    wch
    wth
    wa
    wa
    wph
    wps
    wch
    wth
    bnj248
    @0
    wch
    wth
    anass
    bitri
end
