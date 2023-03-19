include "simpr.mm"

theorem axia2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) -> ps )

  proof
    wph
    wps
    simpr
end
