include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cofs.mm"
include "wbr.mm"
include "cbtwn.mm"
include "wa.mm"
include "ccgr.mm"
include "ccgr3.mm"
include "brofs.mm"
include "simpr1l.mm"
include "simpr2l.mm"
include "simpr1.mm"
include "simpr2.mm"
include "jca.mm"
include "ex.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp23.mm"
include "simp31.mm"
include "simp32.mm"
include "cgrextend.mm"
include "syl133anc.mm"
include "syld.mm"
include "imp.mm"
include "simpr2r.mm"
include "3jca.mm"
include "wb.mm"
include "brcgr3.mm"
include "sylibrd.mm"
include "simpr3.mm"
include "3simpa.mm"
include "btwnxfr.mm"
include "syl5.mm"
include "3simpb.mm"
include "syl6bi.mm"
include "3ad2antr2.mm"
include "impbida.mm"
include "bitrd.mm"

theorem brofs2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\ ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) -> ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg <. <. E , F >. , <. G , H >. >. <-> ( B Btwn <. A , C >. /\ <. A , <. B , C >. >. Cgr3 <. E , <. F , G >. >. /\ ( <. A , D >. Cgr <. E , H >. /\ <. B , D >. Cgr <. F , H >. ) ) ) )

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
    cC
    cD
    cop
    cop
    cE
    cF
    cop
    #
    cG
    cH
    cop
    cop
    cofs
    wbr
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    cF
    cE
    cG
    cop
    #
    cbtwn
    wbr
    #
    wa
    #
    @14
    @15
    ccgr
    wbr
    #
    cB
    cC
    cop
    #
    cF
    cG
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cA
    cD
    cop
    cE
    cH
    cop
    ccgr
    wbr
    cB
    cD
    cop
    cF
    cH
    cop
    ccgr
    wbr
    wa
    #
    w3a
    #
    @17
    cA
    @22
    cop
    cE
    @23
    cop
    ccgr3
    wbr
    #
    @26
    w3a
    #
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cN
    brofs
    @13
    @27
    @29
    @13
    @27
    wa
    #
    @17
    @28
    @26
    @17
    @19
    @25
    @26
    @13
    simpr1l
    @13
    @27
    @28
    @13
    @27
    @21
    @16
    @18
    ccgr
    wbr
    #
    @24
    w3a
    #
    @28
    @13
    @27
    @32
    @30
    @21
    @31
    @24
    @21
    @24
    @20
    @26
    @13
    simpr2l
    @13
    @27
    @31
    @13
    @27
    @20
    @25
    wa
    #
    @31
    @13
    @27
    @33
    @30
    @20
    @25
    @13
    @20
    @25
    @26
    simpr1
    @13
    @20
    @25
    @26
    simpr2
    jca
    ex
    @13
    @0
    @2
    @3
    @5
    @7
    @9
    @10
    @33
    @31
    wi
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
    simp21
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
    @4
    @8
    @9
    @10
    @11
    simp32
    #
    cA
    cB
    cC
    cE
    cF
    cG
    cN
    cgrextend
    syl133anc
    syld
    imp
    @21
    @24
    @20
    @26
    @13
    simpr2r
    3jca
    ex
    @13
    @0
    @2
    @3
    @5
    @7
    @9
    @10
    @28
    @32
    wb
    @34
    @35
    @36
    @37
    @38
    @39
    @40
    cA
    cB
    cC
    cE
    cF
    cG
    cN
    brcgr3
    syl133anc
    #
    sylibrd
    imp
    @13
    @20
    @25
    @26
    simpr3
    3jca
    @13
    @29
    wa
    #
    @20
    @25
    @26
    @42
    @17
    @19
    @13
    @17
    @28
    @26
    simpr1
    @13
    @29
    @19
    @29
    @17
    @28
    wa
    #
    @13
    @19
    @17
    @28
    @26
    3simpa
    @13
    @0
    @2
    @3
    @5
    @7
    @9
    @10
    @43
    @19
    wi
    @34
    @35
    @36
    @37
    @38
    @39
    @40
    cA
    cB
    cC
    cE
    cF
    cG
    cN
    btwnxfr
    syl133anc
    syl5
    imp
    jca
    @13
    @17
    @28
    @25
    @26
    @13
    @28
    @25
    @13
    @28
    @32
    @25
    @41
    @21
    @31
    @24
    3simpb
    syl6bi
    imp
    3ad2antr2
    @13
    @17
    @28
    @26
    simpr3
    3jca
    impbida
    bitrd
end
