include "wex.mm"
include "19.8a.mm"
include "syl.mm"

theorem 19.23bi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.23bi.1: |- ( E. x ph -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wph
    vx
    wex
    wps
    wph
    vx
    19.8a
    19.23bi.1
    syl
end
