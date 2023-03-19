include "atbiffatnnb.mm"

theorem atbiffatnnbalt
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ph -> ps ) -> ( ph -> -. -. ps ) )

  proof
    wph
    wps
    atbiffatnnb
end
