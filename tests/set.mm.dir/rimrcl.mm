include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "crh.mm"
include "co.mm"
include "wcel.mm"
include "crab.mm"
include "crs.mm"
include "df-rngiso.mm"
include "elmpt2cl.mm"

theorem rimrcl
  let cR: class R
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let cV: class V
  let cW: class W


  assert |- ( F e. ( R RingIso S ) -> ( R e. _V /\ S e. _V ) )

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
    crh
    co
    wcel
    vf
    @1
    @0
    crh
    co
    crab
    cR
    cS
    crs
    cF
    vf
    vs
    vr
    df-rngiso
    elmpt2cl
end
