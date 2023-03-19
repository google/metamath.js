include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "bnj290.mm"
include "df-bnj17.mm"
include "bitri.mm"

theorem bnj291
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ph /\ ch /\ th ) /\ ps ) )

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
    wth
    w3a
    wps
    wa
    wph
    wps
    wch
    wth
    bnj290
    wph
    wch
    wth
    wps
    df-bnj17
    bitri
end
