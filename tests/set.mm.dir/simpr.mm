include "idd.mm"
include "imp.mm"

theorem simpr
  let wph: wff ph
  let wps: wff ps


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
