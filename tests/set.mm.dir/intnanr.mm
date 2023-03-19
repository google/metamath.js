include "wa.mm"
include "simpl.mm"
include "mto.mm"

theorem intnanr
  let wph: wff ph
  let wps: wff ps
  assume intnan.1: |- -. ph


  assert |- -. ( ph /\ ps )

  proof
    wph
    wps
    wa
    wph
    intnan.1
    wph
    wps
    simpl
    mto
end
