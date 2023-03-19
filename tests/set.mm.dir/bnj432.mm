include "w-bnj17.mm"
include "wa.mm"
include "bnj422.mm"
include "bnj256.mm"
include "bitri.mm"

theorem bnj432
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ch /\ th ) /\ ( ph /\ ps ) ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wch
    wth
    wph
    wps
    w-bnj17
    wch
    wth
    wa
    wph
    wps
    wa
    wa
    wph
    wps
    wch
    wth
    bnj422
    wch
    wth
    wph
    wps
    bnj256
    bitri
end
