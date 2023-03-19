include "w-bnj17.mm"
include "bnj706.mm"
include "sylbi.mm"

theorem bnj770
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bnj770.1: |- ( et <-> ( ph /\ ps /\ ch /\ th ) )
  assume bnj770.2: |- ( ps -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wch
    wth
    w-bnj17
    wta
    bnj770.1
    wph
    wps
    wch
    wth
    wta
    bnj770.2
    bnj706
    sylbi
end
