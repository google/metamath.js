include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "simplr.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "id.mm"
include "sumex.mm"
include "fvmptd.mm"

theorem eulerpartlemsv1
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint R f
  disjoint R k
  assert |- ( A e. ( ( NN0 ^m NN ) i^i R ) -> ( S ` A ) = sum_ k e. NN ( ( A ` k ) x. k ) )

  proof
    cA
    cn0
    cn
    cmap
    co
    cR
    cin
    #
    wcel
    #
    vf
    cA
    cn
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    @2
    cmul
    co
    #
    vk
    csu
    #
    cn
    @2
    cA
    cfv
    #
    @2
    cmul
    co
    #
    vk
    csu
    #
    @0
    cS
    cvv
    cS
    vf
    @0
    @6
    cmpt
    wceq
    @1
    eulerpartlems.s
    a1i
    @1
    @3
    cA
    wceq
    #
    wa
    #
    cn
    @5
    @8
    vk
    @11
    @2
    cn
    wcel
    #
    wa
    #
    @4
    @7
    @2
    cmul
    @13
    @2
    @3
    cA
    @1
    @10
    @12
    simplr
    fveq1d
    oveq1d
    sumeq2dv
    @1
    id
    @9
    cvv
    wcel
    @1
    cn
    @8
    vk
    sumex
    a1i
    fvmptd
end
