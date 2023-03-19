include "w-bnj17.mm"
include "bnj705.mm"
include "sylbi.mm"

theorem bnj769
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bnj769.1: |- ( et <-> ( ph /\ ps /\ ch /\ th ) )
  assume bnj769.2: |- ( ph -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wch
    wth
    w-bnj17
    wta
    bnj769.1
    wph
    wps
    wch
    wth
    wta
    bnj769.2
    bnj705
    sylbi
end
