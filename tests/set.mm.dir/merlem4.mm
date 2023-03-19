include "wi.mm"
include "wn.mm"
include "meredith.mm"
include "merlem3.mm"
include "ax-mp.mm"

theorem merlem4
  let wph: wff ph
  let wth: wff th
  let wta: wff ta


  assert |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) )

  proof
    wph
    wph
    wi
    wth
    wn
    #
    @0
    wi
    wi
    wth
    wi
    #
    wta
    wi
    wta
    wph
    wi
    wth
    wph
    wi
    wi
    #
    wi
    wta
    @2
    wi
    wph
    wph
    wth
    wth
    wta
    meredith
    @2
    @1
    wta
    merlem3
    ax-mp
end
