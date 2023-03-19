include "intnanr.mm"

theorem notatnand
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume notatnand.1: |- -. ph


  assert |- -. ( ph /\ ps )

  proof
    wph
    wps
    notatnand.1
    intnanr
end
