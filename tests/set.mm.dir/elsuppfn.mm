include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "wa.mm"
include "suppvalfn.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elsuppfn
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vi: setvar i


  assert |- ( ( F Fn X /\ X e. V /\ Z e. W ) -> ( S e. ( F supp Z ) <-> ( S e. X /\ ( F ` S ) =/= Z ) ) )

  proof
    cF
    cX
    wfn
    cX
    cV
    wcel
    cZ
    cW
    wcel
    w3a
    #
    cS
    cF
    cZ
    csupp
    co
    #
    wcel
    cS
    vi
    cv
    #
    cF
    cfv
    #
    cZ
    wne
    #
    vi
    cX
    crab
    #
    wcel
    cS
    cX
    wcel
    cS
    cF
    cfv
    #
    cZ
    wne
    #
    wa
    @0
    @1
    @5
    cS
    vi
    cF
    cV
    cW
    cX
    cZ
    suppvalfn
    eleq2d
    @4
    @7
    vi
    cS
    cX
    @2
    cS
    wceq
    @3
    @6
    cZ
    @2
    cS
    cF
    fveq2
    neeq1d
    elrab
    syl6bb
end
