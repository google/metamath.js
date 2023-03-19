include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "claut.mm"
include "eqid.mm"
include "isldil.mm"
include "simpr.mm"
include "syl6bi.mm"
include "breq1.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "impd.mm"
include "syl6.mm"
include "3imp.mm"

theorem ldilval
  let cB: class B
  let cD: class D
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume ldilval.b: |- B = ( Base ` K )
  assume ldilval.l: |- .<_ = ( le ` K )
  assume ldilval.h: |- H = ( LHyp ` K )
  assume ldilval.d: |- D = ( ( LDil ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. D /\ ( X e. B /\ X .<_ W ) ) -> ( F ` X ) = X )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cD
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    cX
    cF
    cfv
    #
    cX
    wceq
    #
    @0
    @1
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    @7
    cF
    cfv
    #
    @7
    wceq
    #
    wi
    #
    vx
    cB
    wral
    #
    @4
    @6
    wi
    @0
    @1
    cF
    cK
    claut
    cfv
    #
    wcel
    #
    @12
    wa
    @12
    vx
    cB
    cV
    cD
    cF
    cH
    @13
    cK
    c.le
    cW
    ldilval.b
    ldilval.l
    ldilval.h
    @13
    eqid
    ldilval.d
    isldil
    @14
    @12
    simpr
    syl6bi
    @12
    @2
    @3
    @6
    @11
    @3
    @6
    wi
    vx
    cX
    cB
    @7
    cX
    wceq
    #
    @8
    @3
    @10
    @6
    @7
    cX
    cW
    c.le
    breq1
    @15
    @9
    @5
    @7
    cX
    @7
    cX
    cF
    fveq2
    @15
    id
    eqeq12d
    imbi12d
    rspccv
    impd
    syl6
    3imp
end
