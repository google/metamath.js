include "w-bnj17.mm"
include "bnj642.mm"
include "sylbi.mm"

theorem bnj1232
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj1232.1: |- ( ph <-> ( ps /\ ch /\ th /\ ta ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wth
    wta
    w-bnj17
    wps
    bnj1232.1
    wps
    wch
    wth
    wta
    bnj642
    sylbi
end
