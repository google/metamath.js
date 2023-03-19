include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "bnj345.mm"
include "df-bnj17.mm"
include "bitr3i.mm"

theorem bnj446
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ps /\ ch /\ th ) /\ ph ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wps
    wch
    wth
    wph
    w-bnj17
    wps
    wch
    wth
    w3a
    wph
    wa
    wps
    wch
    wth
    wph
    bnj345
    wps
    wch
    wth
    wph
    df-bnj17
    bitr3i
end
