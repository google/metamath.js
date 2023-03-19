include "w3a.mm"
include "3ancoma.mm"
include "3anrot.mm"
include "bitr4i.mm"

theorem 3anrev
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) )

  proof
    wph
    wps
    wch
    w3a
    wps
    wph
    wch
    w3a
    wch
    wps
    wph
    w3a
    wph
    wps
    wch
    3ancoma
    wch
    wps
    wph
    3anrot
    bitr4i
end
