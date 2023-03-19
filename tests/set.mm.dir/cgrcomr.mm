include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wb.mm"
include "cgrcoml.mm"
include "3com23.mm"
include "cgrcom.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3r.mm"
include "simp3l.mm"
include "syl122anc.mm"
include "3bitr4d.mm"

theorem cgrcomr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. <-> <. A , B >. Cgr <. D , C >. ) )

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
    cC
    cD
    cop
    #
    cA
    cB
    cop
    #
    ccgr
    wbr
    #
    cD
    cC
    cop
    #
    @10
    ccgr
    wbr
    #
    @10
    @9
    ccgr
    wbr
    @10
    @12
    ccgr
    wbr
    #
    @0
    @7
    @4
    @11
    @13
    wb
    cC
    cD
    cA
    cB
    cN
    cgrcoml
    3com23
    cA
    cB
    cC
    cD
    cN
    cgrcom
    @8
    @0
    @2
    @3
    @6
    @5
    @14
    @13
    wb
    @0
    @4
    @7
    simp1
    @0
    @2
    @3
    @7
    simp2l
    @0
    @2
    @3
    @7
    simp2r
    @0
    @4
    @5
    @6
    simp3r
    @0
    @4
    @5
    @6
    simp3l
    cA
    cB
    cD
    cC
    cN
    cgrcom
    syl122anc
    3bitr4d
end
