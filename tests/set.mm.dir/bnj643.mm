include "w-bnj17.mm"
include "w3a.mm"
include "bnj291.mm"
include "simprbi.mm"

theorem bnj643
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ps )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wch
    wth
    w3a
    wps
    wph
    wps
    wch
    wth
    bnj291
    simprbi
end
