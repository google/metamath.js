include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "axcgrrflx.mm"
include "3com23.mm"
include "cgrtr4d.mm"

theorem cgrrflx
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> <. A , B >. Cgr <. A , B >. )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    cB
    cA
    cA
    cB
    cA
    cB
    cN
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp3
    #
    @0
    @2
    @3
    simp2
    #
    @5
    @4
    @5
    @4
    @0
    @3
    @2
    cB
    cA
    cop
    cA
    cB
    cop
    ccgr
    wbr
    cB
    cA
    cN
    axcgrrflx
    3com23
    #
    @6
    cgrtr4d
end
