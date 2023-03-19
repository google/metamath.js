include "w-bnj17.mm"
include "bnj645.mm"
include "syl.mm"

theorem bnj708
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj708.1: |- ( th -> ta )


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wth
    wta
    wph
    wps
    wch
    wth
    bnj645
    bnj708.1
    syl
end
