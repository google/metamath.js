include "wn.mm"
include "idd.mm"
include "notnotb.mm"
include "syl6ib.mm"
include "a2i.mm"

theorem atbiffatnnb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ph -> ps ) -> ( ph -> -. -. ps ) )

  proof
    wph
    wps
    wps
    wn
    wn
    #
    wph
    wps
    wps
    @0
    wph
    wps
    idd
    wps
    notnotb
    syl6ib
    a2i
end
