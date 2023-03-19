include "w-bnj17.mm"
include "w3a.mm"
include "df-bnj17.mm"
include "simplbi.mm"

theorem bnj658
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> ( ph /\ ps /\ ch ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    w3a
    wth
    wph
    wps
    wch
    wth
    df-bnj17
    simplbi
end
