include "wa.mm"
include "iba.mm"
include "pm5.74i.mm"

theorem ancrb
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) )

  proof
    wph
    wps
    wps
    wph
    wa
    wph
    wps
    iba
    pm5.74i
end
