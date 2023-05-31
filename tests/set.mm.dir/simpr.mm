include "idd.mm"
include "imp.mm"

theorem simpr
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph /\ ps ) -> ps )

  proof
    wph
    wps
    wps
    wph
    wps
    idd
    imp
end
