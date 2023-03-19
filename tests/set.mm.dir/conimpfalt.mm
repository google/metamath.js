include "aibnbaif.mm"

theorem conimpfalt
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume conimpfalt.1: |- ph
  assume conimpfalt.2: |- -. ps
  assume conimpfalt.3: |- ( ph -> ps )


  assert |- ( ph <-> F. )

  proof
    wph
    wps
    conimpfalt.3
    conimpfalt.2
    aibnbaif
end
