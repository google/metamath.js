include "w-bnj17.mm"
include "bnj345.mm"
include "bitri.mm"

theorem bnj422
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ch /\ th /\ ph /\ ps ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wth
    wph
    wps
    wch
    w-bnj17
    wch
    wth
    wph
    wps
    w-bnj17
    wph
    wps
    wch
    wth
    bnj345
    wth
    wph
    wps
    wch
    bnj345
    bitri
end
