include "id.mm"
include "bnj771.mm"

theorem bnj1247
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj1247.1: |- ( ph <-> ( ps /\ ch /\ th /\ ta ) )


  assert |- ( ph -> th )

  proof
    wps
    wch
    wth
    wta
    wth
    wph
    bnj1247.1
    wth
    id
    bnj771
end
