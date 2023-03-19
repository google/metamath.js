include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "anandi.mm"
include "bitri.mm"

theorem anandi3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wch
    wa
    wa
    wph
    wps
    wa
    wph
    wch
    wa
    wa
    wph
    wps
    wch
    3anass
    wph
    wps
    wch
    anandi
    bitri
end
