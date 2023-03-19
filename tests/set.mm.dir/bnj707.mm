include "w-bnj17.mm"
include "w3a.mm"
include "bnj258.mm"
include "simprbi.mm"
include "syl.mm"

theorem bnj707
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj707.1: |- ( ch -> ta )


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    #
    wch
    wta
    @0
    wph
    wps
    wth
    w3a
    wch
    wph
    wps
    wch
    wth
    bnj258
    simprbi
    bnj707.1
    syl
end
