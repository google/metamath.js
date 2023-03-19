include "wi.mm"
include "wn.mm"
include "meredith.mm"
include "merlem9.mm"
include "ax-mp.mm"

theorem merlem10
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) )

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
    wth
    @3
    wi
    wi
    #
    wph
    wph
    wph
    wph
    wph
    meredith
    @3
    wph
    wi
    @1
    wth
    wn
    wi
    wi
    wph
    wi
    #
    wph
    wi
    @5
    wi
    @2
    @5
    wi
    @3
    wph
    wph
    wth
    wph
    meredith
    @6
    wph
    @4
    wth
    wps
    @2
    merlem9
    ax-mp
    ax-mp
end
