include "wa.mm"
include "pm3.21.mm"
include "a2i.mm"

theorem ancr
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) )

  proof
    wph
    wps
    wps
    wph
    wa
    wph
    wps
    pm3.21
    a2i
end
