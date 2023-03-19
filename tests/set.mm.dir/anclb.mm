include "wa.mm"
include "ibar.mm"
include "pm5.74i.mm"

theorem anclb
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wa
    wph
    wps
    ibar
    pm5.74i
end
