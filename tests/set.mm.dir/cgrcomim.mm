include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "simpr.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "cgrrflxd.mm"
include "cgrtr4and.mm"
include "ex.mm"

theorem cgrcomim
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. -> <. C , D >. Cgr <. A , B >. ) )

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
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    @10
    @9
    ccgr
    wbr
    @8
    @11
    cA
    cB
    cC
    cD
    cA
    cB
    cN
    @0
    @4
    @7
    simp1
    @0
    @2
    @3
    @7
    simp2l
    #
    @0
    @2
    @3
    @7
    simp2r
    #
    @0
    @4
    @5
    @6
    simp3l
    @0
    @4
    @5
    @6
    simp3r
    @12
    @13
    @8
    @11
    simpr
    @8
    @11
    wa
    cA
    cB
    cN
    @0
    @4
    @7
    @11
    simpl1
    @2
    @3
    @0
    @7
    @11
    simpl2l
    @2
    @3
    @0
    @7
    @11
    simpl2r
    cgrrflxd
    cgrtr4and
    ex
end
