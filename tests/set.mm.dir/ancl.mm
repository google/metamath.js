include "wa.mm"
include "pm3.2.mm"
include "a2i.mm"

theorem ancl
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wa
    wph
    wps
    pm3.2
    a2i
end
