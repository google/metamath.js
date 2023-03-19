include "aibnbaif.mm"

theorem conimpf
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume conimpf.1: |- ph
  assume conimpf.2: |- -. ps
  assume conimpf.3: |- ( ph -> ps )


  assert |- ( ph <-> F. )

  proof
    wph
    wps
    conimpf.3
    conimpf.2
    aibnbaif
end
