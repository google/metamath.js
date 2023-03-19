include "wn.mm"
include "wi.mm"
include "merlem11.mm"
include "merlem1.mm"
include "ax-mp.mm"

theorem luk-3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ph -> ps ) )

  proof
    wph
    wn
    #
    @0
    wps
    wi
    #
    wi
    @1
    wi
    wph
    @1
    wi
    @0
    wps
    merlem11
    wph
    wps
    @0
    @1
    merlem1
    ax-mp
end
