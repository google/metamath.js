include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wa.mm"
include "csegle.mm"
include "df-3an.mm"
include "seglecgr12im.mm"
include "syl5bir.mm"
include "expd.mm"
include "wi.mm"
include "wb.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp23.mm"
include "simp31.mm"
include "cgrcom.mm"
include "syl122anc.mm"
include "simp21.mm"
include "simp22.mm"
include "simp32.mm"
include "simp33.mm"
include "anbi12d.mm"
include "syl333anc.mm"
include "sylbid.mm"
include "impbidd.mm"

theorem seglecgr12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\ ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) -> ( ( <. A , B >. Cgr <. E , F >. /\ <. C , D >. Cgr <. G , H >. ) -> ( <. A , B >. Seg<_ <. C , D >. <-> <. E , F >. Seg<_ <. G , H >. ) ) )

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
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    w3a
    #
    cF
    @1
    wcel
    #
    cG
    @1
    wcel
    #
    cH
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cA
    cB
    cop
    #
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    cC
    cD
    cop
    #
    cG
    cH
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    @14
    @17
    csegle
    wbr
    #
    @15
    @18
    csegle
    wbr
    #
    @13
    @20
    @21
    @22
    @20
    @21
    wa
    @16
    @19
    @21
    w3a
    @13
    @22
    @16
    @19
    @21
    df-3an
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cN
    seglecgr12im
    syl5bir
    expd
    @13
    @20
    @15
    @14
    ccgr
    wbr
    #
    @18
    @17
    ccgr
    wbr
    #
    wa
    #
    @22
    @21
    wi
    @13
    @16
    @23
    @19
    @24
    @13
    @0
    @2
    @3
    @7
    @9
    @16
    @23
    wb
    @0
    @2
    @3
    @8
    @12
    simp11
    #
    @0
    @2
    @3
    @8
    @12
    simp12
    #
    @0
    @2
    @3
    @8
    @12
    simp13
    #
    @4
    @5
    @6
    @7
    @12
    simp23
    #
    @4
    @8
    @9
    @10
    @11
    simp31
    #
    cA
    cB
    cE
    cF
    cN
    cgrcom
    syl122anc
    @13
    @0
    @5
    @6
    @10
    @11
    @19
    @24
    wb
    @26
    @4
    @5
    @6
    @7
    @12
    simp21
    #
    @4
    @5
    @6
    @7
    @12
    simp22
    #
    @4
    @8
    @9
    @10
    @11
    simp32
    #
    @4
    @8
    @9
    @10
    @11
    simp33
    #
    cC
    cD
    cG
    cH
    cN
    cgrcom
    syl122anc
    anbi12d
    @13
    @25
    @22
    @21
    @25
    @22
    wa
    @23
    @24
    @22
    w3a
    #
    @13
    @21
    @23
    @24
    @22
    df-3an
    @13
    @0
    @7
    @9
    @10
    @11
    @2
    @3
    @5
    @6
    @35
    @21
    wi
    @26
    @29
    @30
    @33
    @34
    @27
    @28
    @31
    @32
    cE
    cF
    cG
    cH
    cA
    cB
    cC
    cD
    cN
    seglecgr12im
    syl333anc
    syl5bir
    expd
    sylbid
    impbidd
end
