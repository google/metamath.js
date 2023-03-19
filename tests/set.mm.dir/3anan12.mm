include "w3a.mm"
include "wa.mm"
include "3ancoma.mm"
include "3anass.mm"
include "bitri.mm"

theorem 3anan12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    w3a
    wps
    wph
    wch
    w3a
    wps
    wph
    wch
    wa
    wa
    wph
    wps
    wch
    3ancoma
    wps
    wph
    wch
    3anass
    bitri
end
