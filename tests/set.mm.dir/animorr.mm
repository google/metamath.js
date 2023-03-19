include "wa.mm"
include "simpr.mm"
include "olcd.mm"

theorem animorr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps ) -> ( ch \/ ps ) )

  proof
    wph
    wps
    wa
    wps
    wch
    wph
    wps
    simpr
    olcd
end
