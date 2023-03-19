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
include "cgrrflx2d.mm"
include "wi.mm"
include "simp3l.mm"
include "simp3r.mm"
include "axcgrtr.mm"
include "syl133anc.mm"
include "mpand.mm"
include "impbid.mm"

theorem cgrcoml
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. <-> <. B , A >. Cgr <. C , D >. ) )

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
    cB
    cA
    cop
    #
    @10
    ccgr
    wbr
    #
    @8
    @9
    @12
    ccgr
    wbr
    #
    @11
    @13
    @8
    cA
    cB
    cN
    @0
    @4
    @7
    simp1
    #
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
    cgrrflx2d
    @8
    @0
    @2
    @3
    @3
    @2
    @5
    @6
    @14
    @11
    wa
    @13
    wi
    @15
    @16
    @17
    @17
    @16
    @0
    @4
    @5
    @6
    simp3l
    #
    @0
    @4
    @5
    @6
    simp3r
    #
    cA
    cB
    cB
    cA
    cC
    cD
    cN
    axcgrtr
    syl133anc
    mpand
    @8
    @12
    @9
    ccgr
    wbr
    #
    @13
    @11
    @8
    cB
    cA
    cN
    @15
    @17
    @16
    cgrrflx2d
    @8
    @0
    @3
    @2
    @2
    @3
    @5
    @6
    @20
    @13
    wa
    @11
    wi
    @15
    @17
    @16
    @16
    @17
    @18
    @19
    cB
    cA
    cA
    cB
    cC
    cD
    cN
    axcgrtr
    syl133anc
    mpand
    impbid
end
