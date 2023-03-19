include "w-bnj17.mm"
include "bnj642.mm"
include "syl.mm"

theorem bnj705
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj705.1: |- ( ph -> ta )


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wta
    wph
    wps
    wch
    wth
    bnj642
    bnj705.1
    syl
end
