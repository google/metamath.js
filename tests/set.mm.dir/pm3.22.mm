include "wa.mm"
include "pm3.21.mm"
include "imp.mm"

theorem pm3.22
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph /\ ps ) -> ( ps /\ ph ) )

  proof
    wph
    wps
    wps
    wph
    wa
    wph
    wps
    pm3.21
    imp
end
