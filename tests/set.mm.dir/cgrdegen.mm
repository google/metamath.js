include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "opeq1.mm"
include "breq1d.mm"
include "biimpac.mm"
include "wi.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "cgrid2.mm"
include "syl13anc.mm"
include "syl5.mm"
include "expdimp.mm"
include "breq2d.mm"
include "simp2l.mm"
include "axcgrid.mm"
include "impbid.mm"
include "ex.mm"

theorem cgrdegen
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. -> ( A = B <-> C = D ) ) )

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
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    wb
    @8
    @11
    wa
    @12
    @13
    @8
    @11
    @12
    @13
    @11
    @12
    wa
    cB
    cB
    cop
    #
    @10
    ccgr
    wbr
    #
    @8
    @13
    @12
    @11
    @15
    @12
    @9
    @14
    @10
    ccgr
    cA
    cB
    cB
    opeq1
    breq1d
    biimpac
    @8
    @0
    @3
    @5
    @6
    @15
    @13
    wi
    @0
    @4
    @7
    simp1
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
    #
    cB
    cC
    cD
    cN
    cgrid2
    syl13anc
    syl5
    expdimp
    @8
    @11
    @13
    @12
    @11
    @13
    wa
    @9
    cD
    cD
    cop
    #
    ccgr
    wbr
    #
    @8
    @12
    @13
    @11
    @20
    @13
    @10
    @19
    @9
    ccgr
    cC
    cD
    cD
    opeq1
    breq2d
    biimpac
    @8
    @0
    @2
    @3
    @6
    @20
    @12
    wi
    @16
    @0
    @2
    @3
    @7
    simp2l
    @17
    @18
    cA
    cB
    cD
    cN
    axcgrid
    syl13anc
    syl5
    expdimp
    impbid
    ex
end
