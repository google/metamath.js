include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "creverse.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "revval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem revfv
  let cA: class A
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x


  assert |- ( ( W e. Word A /\ X e. ( 0 ..^ ( # ` W ) ) ) -> ( ( reverse ` W ) ` X ) = ( W ` ( ( ( # ` W ) - 1 ) - X ) ) )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    cX
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    cX
    cW
    creverse
    cfv
    #
    cfv
    cX
    vx
    @3
    @2
    c1
    cmin
    co
    #
    vx
    cv
    #
    cmin
    co
    #
    cW
    cfv
    #
    cmpt
    #
    cfv
    @5
    cX
    cmin
    co
    #
    cW
    cfv
    #
    @1
    cX
    @4
    @9
    vx
    @0
    cW
    revval
    fveq1d
    vx
    cX
    @8
    @11
    @3
    @9
    @6
    cX
    wceq
    @7
    @10
    cW
    @6
    cX
    @5
    cmin
    oveq2
    fveq2d
    @9
    eqid
    @10
    cW
    fvex
    fvmpt
    sylan9eq
end
