include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "anass.mm"
include "bitri.mm"

theorem 3anass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    wch
    wa
    wph
    wps
    wch
    wa
    wa
    wph
    wps
    wch
    df-3an
    wph
    wps
    wch
    anass
    bitri
end
