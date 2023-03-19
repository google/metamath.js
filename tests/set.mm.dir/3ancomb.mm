include "w3a.mm"
include "3ancoma.mm"
include "3anrot.mm"
include "bitri.mm"

theorem 3ancomb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) )

  proof
    wph
    wps
    wch
    w3a
    wps
    wph
    wch
    w3a
    wph
    wch
    wps
    w3a
    wph
    wps
    wch
    3ancoma
    wps
    wph
    wch
    3anrot
    bitri
end
