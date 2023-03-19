include "wtru.mm"
include "bitr4i.mm"

theorem bothtbothsame
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume bothtbothsame.1: |- ( ph <-> T. )
  assume bothtbothsame.2: |- ( ps <-> T. )


  assert |- ( ph <-> ps )

  proof
    wph
    wtru
    wps
    bothtbothsame.1
    bothtbothsame.2
    bitr4i
end
