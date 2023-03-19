include "aibnbna.mm"
include "bifal.mm"

theorem aibnbaif
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aibnbaif.1: |- ( ph -> ps )
  assume aibnbaif.2: |- -. ps


  assert |- ( ph <-> F. )

  proof
    wph
    wph
    wps
    aibnbaif.1
    aibnbaif.2
    aibnbna
    bifal
end
