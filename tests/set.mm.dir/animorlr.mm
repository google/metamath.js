include "wa.mm"
include "simpl.mm"
include "olcd.mm"

theorem animorlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps ) -> ( ch \/ ph ) )

  proof
    wph
    wps
    wa
    wph
    wch
    wph
    wps
    simpl
    olcd
end
