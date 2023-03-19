include "w-bnj17.mm"
include "bnj643.mm"
include "syl.mm"

theorem bnj706
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj706.1: |- ( ps -> ta )


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wps
    wta
    wph
    wps
    wch
    wth
    bnj643
    bnj706.1
    syl
end
