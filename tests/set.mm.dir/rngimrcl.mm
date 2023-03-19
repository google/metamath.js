include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "crab.mm"
include "crngs.mm"
include "df-rngisom.mm"
include "elmpt2cl.mm"

theorem rngimrcl
  let cR: class R
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( F e. ( R RngIsom S ) -> ( R e. _V /\ S e. _V ) )

  proof
    vr
    vs
    cvv
    cvv
    vf
    cv
    ccnv
    vs
    cv
    #
    vr
    cv
    #
    crngh
    co
    wcel
    vf
    @1
    @0
    crngh
    co
    crab
    cR
    cS
    crngs
    cF
    vf
    vs
    vr
    df-rngisom
    elmpt2cl
end
