include "wfal.mm"
include "bitr4i.mm"

theorem bothfbothsame
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume bothfbothsame.1: |- ( ph <-> F. )
  assume bothfbothsame.2: |- ( ps <-> F. )


  assert |- ( ph <-> ps )

  proof
    wph
    wfal
    wps
    bothfbothsame.1
    bothfbothsame.2
    bitr4i
end
