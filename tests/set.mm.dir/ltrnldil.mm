include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "eqid.mm"
include "isltrn.mm"
include "simprbda.mm"

theorem ltrnldil
  let cD: class D
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  assume ltrnldil.h: |- H = ( LHyp ` K )
  assume ltrnldil.d: |- D = ( ( LDil ` K ) ` W )
  assume ltrnldil.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T ) -> F e. D )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cF
    cD
    wcel
    vp
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    vq
    cv
    #
    cW
    @1
    wbr
    wn
    wa
    @0
    @0
    cF
    cfv
    cK
    cjn
    cfv
    #
    co
    cW
    cK
    cmee
    cfv
    #
    co
    @2
    @2
    cF
    cfv
    @3
    co
    cW
    @4
    co
    wceq
    wi
    vq
    cK
    catm
    cfv
    #
    wral
    vp
    @5
    wral
    @5
    cV
    cD
    cT
    cF
    cH
    @3
    cK
    @1
    @4
    cW
    vq
    vp
    @1
    eqid
    @3
    eqid
    @4
    eqid
    @5
    eqid
    ltrnldil.h
    ltrnldil.d
    ltrnldil.t
    isltrn
    simprbda
end
