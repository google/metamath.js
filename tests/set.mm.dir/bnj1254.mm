include "w-bnj17.mm"
include "id.mm"
include "bnj708.mm"
include "sylbi.mm"

theorem bnj1254
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj1254.1: |- ( ph <-> ( ps /\ ch /\ th /\ ta ) )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    w-bnj17
    wta
    bnj1254.1
    wps
    wch
    wth
    wta
    wta
    wta
    id
    bnj708
    sylbi
end
