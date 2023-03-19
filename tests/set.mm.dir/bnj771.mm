include "w-bnj17.mm"
include "bnj707.mm"
include "sylbi.mm"

theorem bnj771
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bnj771.1: |- ( et <-> ( ph /\ ps /\ ch /\ th ) )
  assume bnj771.2: |- ( ch -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wch
    wth
    w-bnj17
    wta
    bnj771.1
    wph
    wps
    wch
    wth
    wta
    bnj771.2
    bnj707
    sylbi
end
