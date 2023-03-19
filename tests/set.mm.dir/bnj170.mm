include "w3a.mm"
include "wa.mm"
include "3anrot.mm"
include "df-3an.mm"
include "bitri.mm"

theorem bnj170
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ( ps /\ ch ) /\ ph ) )

  proof
    wph
    wps
    wch
    w3a
    wps
    wch
    wph
    w3a
    wps
    wch
    wa
    wph
    wa
    wph
    wps
    wch
    3anrot
    wps
    wch
    wph
    df-3an
    bitri
end
