include "wcel.mm"
include "cvv.mm"
include "creverse.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "id.mm"
include "oveq1d.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "df-reverse.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem revval
  let vx: setvar x
  let cV: class V
  let cW: class W
  let vw: setvar w
  let cA: class A
  let cX: class X

  disjoint W x
  disjoint w x
  disjoint W w
  disjoint A x
  disjoint X x
  assert |- ( W e. V -> ( reverse ` W ) = ( x e. ( 0 ..^ ( # ` W ) ) |-> ( W ` ( ( ( # ` W ) - 1 ) - x ) ) ) )

  proof
    cW
    cV
    wcel
    cW
    cvv
    wcel
    cW
    creverse
    cfv
    vx
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    @0
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
    wceq
    cW
    cV
    elex
    vw
    cW
    vx
    cc0
    vw
    cv
    #
    chash
    cfv
    #
    cfzo
    co
    #
    @8
    c1
    cmin
    co
    #
    @3
    cmin
    co
    #
    @7
    cfv
    #
    cmpt
    @6
    cvv
    creverse
    @7
    cW
    wceq
    #
    vx
    @9
    @12
    @1
    @5
    @13
    @8
    @0
    cc0
    cfzo
    @7
    cW
    chash
    fveq2
    #
    oveq2d
    @13
    @11
    @4
    @7
    cW
    @13
    id
    @13
    @10
    @2
    @3
    cmin
    @13
    @8
    @0
    c1
    cmin
    @14
    oveq1d
    oveq1d
    fveq12d
    mpteq12dv
    vx
    vw
    df-reverse
    vx
    @1
    @5
    cc0
    @0
    cfzo
    ovex
    mptex
    fvmpt
    syl
end
