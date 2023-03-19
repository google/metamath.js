include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "frlmbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem frlmelbas
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmelbas.n: |- N = ( Base ` R )
  assume frlmelbas.z: |- .0. = ( 0g ` R )
  assume frlmelbas.b: |- B = ( Base ` F )


  assert |- ( ( R e. V /\ I e. W ) -> ( X e. B <-> ( X e. ( N ^m I ) /\ X finSupp .0. ) ) )

  proof
    cR
    cV
    wcel
    cI
    cW
    wcel
    wa
    #
    cX
    cB
    wcel
    cX
    vk
    cv
    #
    c.0
    cfsupp
    wbr
    #
    vk
    cN
    cI
    cmap
    co
    #
    crab
    #
    wcel
    cX
    @3
    wcel
    cX
    c.0
    cfsupp
    wbr
    #
    wa
    @0
    cB
    @4
    cX
    @0
    @4
    cF
    cbs
    cfv
    cB
    @4
    cR
    vk
    cF
    cI
    cN
    cV
    cW
    c.0
    frlmval.f
    frlmelbas.n
    frlmelbas.z
    @4
    eqid
    frlmbas
    frlmelbas.b
    syl6reqr
    eleq2d
    @2
    @5
    vk
    cX
    @3
    @1
    cX
    c.0
    cfsupp
    breq1
    elrab
    syl6bb
end
