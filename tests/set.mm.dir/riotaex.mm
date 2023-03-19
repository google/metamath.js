include "crio.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "cvv.mm"
include "df-riota.mm"
include "iotaex.mm"
include "eqeltri.mm"

theorem riotaex
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( iota_ x e. A ps ) e. _V

  proof
    wps
    vx
    cA
    crio
    vx
    cv
    cA
    wcel
    wps
    wa
    #
    vx
    cio
    cvv
    wps
    vx
    cA
    df-riota
    @0
    vx
    iotaex
    eqeltri
end
