include "wa.mm"
include "simpr.mm"
include "orcd.mm"

theorem animorrl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps ) -> ( ps \/ ch ) )

  proof
    wph
    wps
    wa
    wps
    wch
    wph
    wps
    simpr
    orcd
end
