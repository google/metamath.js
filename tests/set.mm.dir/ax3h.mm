include "wn.mm"
include "wi.mm"
include "hirstL-ax3.mm"
include "jarr.mm"
include "syl.mm"

theorem ax3h
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )

  proof
    wph
    wn
    #
    wps
    wn
    wi
    @0
    wps
    wi
    wph
    wi
    wps
    wph
    wi
    wph
    wps
    hirstL-ax3
    @0
    wps
    wph
    jarr
    syl
end
