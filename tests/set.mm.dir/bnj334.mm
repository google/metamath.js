include "w-bnj17.mm"
include "bnj290.mm"
include "bnj257.mm"
include "bnj312.mm"
include "3bitri.mm"

theorem bnj334
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ch /\ ph /\ ps /\ th ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wch
    wth
    wps
    w-bnj17
    wph
    wch
    wps
    wth
    w-bnj17
    wch
    wph
    wps
    wth
    w-bnj17
    wph
    wps
    wch
    wth
    bnj290
    wph
    wch
    wth
    wps
    bnj257
    wph
    wch
    wps
    wth
    bnj312
    3bitri
end
