include "wcel.mm"
include "wa.mm"
include "cldil.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "ltrnldil.mm"
include "3adant3.mm"
include "ldilval.mm"
include "syld3an2.mm"

theorem ltrnval1
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  assume ltrnval1.b: |- B = ( Base ` K )
  assume ltrnval1.l: |- .<_ = ( le ` K )
  assume ltrnval1.h: |- H = ( LHyp ` K )
  assume ltrnval1.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T /\ ( X e. B /\ X .<_ W ) ) -> ( F ` X ) = X )

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
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
    #
    cF
    cT
    wcel
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    cX
    cF
    cfv
    cX
    wceq
    @0
    @3
    @2
    @4
    @1
    cT
    cF
    cH
    cK
    cV
    cW
    ltrnval1.h
    @1
    eqid
    #
    ltrnval1.t
    ltrnldil
    3adant3
    cB
    @1
    cF
    cH
    cK
    c.le
    cV
    cW
    cX
    ltrnval1.b
    ltrnval1.l
    ltrnval1.h
    @5
    ldilval
    syld3an2
end
