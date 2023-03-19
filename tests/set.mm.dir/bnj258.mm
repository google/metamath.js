include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "bnj257.mm"
include "df-bnj17.mm"
include "bitri.mm"

theorem bnj258
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ph /\ ps /\ th ) /\ ch ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wth
    wch
    w-bnj17
    wph
    wps
    wth
    w3a
    wch
    wa
    wph
    wps
    wch
    wth
    bnj257
    wph
    wps
    wth
    wch
    df-bnj17
    bitri
end
