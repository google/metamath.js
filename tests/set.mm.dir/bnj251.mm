include "w-bnj17.mm"
include "wa.mm"
include "bnj250.mm"
include "anass.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem bnj251
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ( ps /\ ( ch /\ th ) ) ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    wa
    wth
    wa
    #
    wa
    wph
    wps
    wch
    wth
    wa
    wa
    #
    wa
    wph
    wps
    wch
    wth
    bnj250
    @0
    @1
    wph
    wps
    wch
    wth
    anass
    anbi2i
    bitri
end
