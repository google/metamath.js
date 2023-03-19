include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cifs.mm"
include "wbr.mm"
include "cbtwn.mm"
include "wa.mm"
include "ccgr.mm"
include "ccgr3.mm"
include "brifs.mm"
include "simpr1l.mm"
include "3simpa.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp23.mm"
include "simp31.mm"
include "simp32.mm"
include "cgrsub.mm"
include "syl133anc.mm"
include "syl5.mm"
include "imp.mm"
include "simpr2l.mm"
include "simpr2r.mm"
include "3jca.mm"
include "ex.mm"
include "wb.mm"
include "brcgr3.mm"
include "sylibrd.mm"
include "simpr3.mm"
include "simpr1.mm"
include "btwnxfr.mm"
include "jca.mm"
include "3simpc.mm"
include "syl6bi.mm"
include "3ad2antr2.mm"
include "impbida.mm"
include "bitrd.mm"

theorem brifs2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\ ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) -> ( <. <. A , B >. , <. C , D >. >. InnerFiveSeg <. <. E , F >. , <. G , H >. >. <-> ( B Btwn <. A , C >. /\ <. A , <. B , C >. >. Cgr3 <. E , <. F , G >. >. /\ ( <. A , D >. Cgr <. E , H >. /\ <. C , D >. Cgr <. G , H >. ) ) ) )

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
    #
    cop
    cE
    cF
    cop
    #
    cG
    cH
    cop
    #
    cop
    cifs
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
    @18
    @20
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
    @15
    @17
    ccgr
    wbr
    wa
    #
    w3a
    #
    @19
    cA
    @24
    cop
    cE
    @25
    cop
    ccgr3
    wbr
    #
    @28
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
    brifs
    @13
    @29
    @31
    @13
    @29
    wa
    #
    @19
    @30
    @28
    @19
    @21
    @27
    @28
    @13
    simpr1l
    @13
    @29
    @30
    @13
    @29
    @14
    @16
    ccgr
    wbr
    #
    @23
    @26
    w3a
    #
    @30
    @13
    @29
    @34
    @32
    @33
    @23
    @26
    @13
    @29
    @33
    @29
    @22
    @27
    wa
    #
    @13
    @33
    @22
    @27
    @28
    3simpa
    @13
    @0
    @2
    @3
    @5
    @7
    @9
    @10
    @35
    @33
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
    cgrsub
    syl133anc
    syl5
    imp
    @23
    @26
    @22
    @28
    @13
    simpr2l
    @23
    @26
    @22
    @28
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
    @30
    @34
    wb
    @36
    @37
    @38
    @39
    @40
    @41
    @42
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
    @22
    @27
    @28
    simpr3
    3jca
    @13
    @31
    wa
    #
    @22
    @27
    @28
    @44
    @19
    @21
    @13
    @19
    @30
    @28
    simpr1
    @13
    @31
    @21
    @31
    @19
    @30
    wa
    #
    @13
    @21
    @19
    @30
    @28
    3simpa
    @13
    @0
    @2
    @3
    @5
    @7
    @9
    @10
    @45
    @21
    wi
    @36
    @37
    @38
    @39
    @40
    @41
    @42
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
    @19
    @30
    @27
    @28
    @13
    @30
    @27
    @13
    @30
    @34
    @27
    @43
    @33
    @23
    @26
    3simpc
    syl6bi
    imp
    3ad2antr2
    @13
    @19
    @30
    @28
    simpr3
    3jca
    impbida
    bitrd
end
