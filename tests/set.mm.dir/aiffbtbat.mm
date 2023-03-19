include "wtru.mm"
include "bitr4i.mm"

theorem aiffbtbat
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aiffbtbat.1: |- ( ph <-> ps )
  assume aiffbtbat.2: |- ( T. <-> ps )


  assert |- ( ph <-> T. )

  proof
    wph
    wps
    wtru
    aiffbtbat.1
    aiffbtbat.2
    bitr4i
end
