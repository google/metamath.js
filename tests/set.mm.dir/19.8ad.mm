include "wex.mm"
include "19.8a.mm"
include "syl.mm"

theorem 19.8ad
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k
  assume 19.8ad.1: |- ( ph -> ps )


  assert |- ( ph -> E. x ps )

  proof
    wph
    wps
    wps
    vx
    wex
    19.8ad.1
    wps
    vx
    19.8a
    syl
end
