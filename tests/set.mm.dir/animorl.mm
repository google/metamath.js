include "wa.mm"
include "simpl.mm"
include "orcd.mm"

theorem animorl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps ) -> ( ph \/ ch ) )

  proof
    wph
    wps
    wa
    wph
    wch
    wph
    wps
    simpl
    orcd
end
