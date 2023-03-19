include "wi.mm"
include "wn.mm"
include "meredith.mm"
include "merlem10.mm"
include "ax-mp.mm"

theorem merlem11
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) )

  proof
    wph
    wph
    wi
    #
    wph
    wn
    #
    @1
    wi
    wi
    wph
    wi
    wph
    wi
    @0
    @0
    wi
    wi
    #
    wph
    wph
    wps
    wi
    #
    wi
    #
    @3
    wi
    #
    wph
    wph
    wph
    wph
    wph
    meredith
    @4
    @5
    wi
    @2
    @5
    wi
    wph
    wps
    @4
    merlem10
    @4
    @3
    @2
    merlem10
    ax-mp
    ax-mp
end
