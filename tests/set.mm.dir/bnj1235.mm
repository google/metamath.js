include "id.mm"
include "bnj770.mm"

theorem bnj1235
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj1235.1: |- ( ph <-> ( ps /\ ch /\ th /\ ta ) )


  assert |- ( ph -> ch )

  proof
    wps
    wch
    wth
    wta
    wch
    wph
    bnj1235.1
    wch
    id
    bnj770
end
