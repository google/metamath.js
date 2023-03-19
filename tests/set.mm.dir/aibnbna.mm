include "mto.mm"

theorem aibnbna
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aibnbna.1: |- ( ph -> ps )
  assume aibnbna.2: |- -. ps


  assert |- -. ph

  proof
    wph
    wps
    aibnbna.2
    aibnbna.1
    mto
end
