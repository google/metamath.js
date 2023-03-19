include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "ellkr.mm"
include "simplbda.mm"
include "3impa.mm"

theorem lkrf0
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lkrf0.d: |- D = ( Scalar ` W )
  assume lkrf0.o: |- .0. = ( 0g ` D )
  assume lkrf0.f: |- F = ( LFnl ` W )
  assume lkrf0.k: |- K = ( LKer ` W )


  assert |- ( ( W e. Y /\ G e. F /\ X e. ( K ` G ) ) -> ( G ` X ) = .0. )

  proof
    cW
    cY
    wcel
    #
    cG
    cF
    wcel
    #
    cX
    cG
    cK
    cfv
    wcel
    #
    cX
    cG
    cfv
    c.0
    wceq
    #
    @0
    @1
    wa
    @2
    cX
    cW
    cbs
    cfv
    #
    wcel
    @3
    cD
    cF
    cG
    cK
    @4
    cW
    cX
    cY
    c.0
    @4
    eqid
    lkrf0.d
    lkrf0.o
    lkrf0.f
    lkrf0.k
    ellkr
    simplbda
    3impa
end
