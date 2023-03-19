include "w-bnj17.mm"
include "w3a.mm"
include "bnj658.mm"
include "syl.mm"

theorem bnj721
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj721.1: |- ( ( ph /\ ps /\ ch ) -> ta )


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ta )

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
    wta
    wph
    wps
    wch
    wth
    bnj658
    bnj721.1
    syl
end
