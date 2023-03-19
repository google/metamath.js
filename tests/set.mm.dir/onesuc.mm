include "com.mm"
include "limom.mm"
include "wcel.mm"
include "csuc.mm"
include "cvv.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "cmpt.mm"
include "c1o.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "frsuc.mm"
include "wceq.mm"
include "peano2.mm"
include "fvres.mm"
include "syl.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "oesuclem.mm"

theorem onesuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. _om ) -> ( A ^o suc B ) = ( ( A ^o B ) .o A ) )

  proof
    vx
    cA
    cB
    com
    limom
    cB
    com
    wcel
    #
    cB
    csuc
    #
    vx
    cvv
    vx
    cv
    cA
    comu
    co
    cmpt
    #
    c1o
    crdg
    #
    com
    cres
    #
    cfv
    #
    cB
    @4
    cfv
    #
    @2
    cfv
    @1
    @3
    cfv
    #
    cB
    @3
    cfv
    #
    @2
    cfv
    c1o
    cB
    @2
    frsuc
    @0
    @1
    com
    wcel
    @5
    @7
    wceq
    cB
    peano2
    @1
    com
    @3
    fvres
    syl
    @0
    @6
    @8
    @2
    cB
    com
    @3
    fvres
    fveq2d
    3eqtr3d
    oesuclem
end
