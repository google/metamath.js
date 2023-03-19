include "w-bnj17.mm"
include "w3a.mm"
include "bnj446.mm"
include "simplbi.mm"

theorem bnj667
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ( ps /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wps
    wch
    wth
    w3a
    wph
    wph
    wps
    wch
    wth
    bnj446
    simplbi
end
