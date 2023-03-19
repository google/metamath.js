include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "ccgr3.mm"
include "wi.mm"
include "wa.mm"
include "cbtwn.mm"
include "w3o.mm"
include "btwnxfr.mm"
include "expcomd.mm"
include "imp.mm"
include "cgr3permute4.mm"
include "biid.mm"
include "3anrot.mm"
include "syl3anbr.mm"
include "sylbid.mm"
include "cgr3permute3.mm"
include "syl3anb.mm"
include "3orim123d.mm"
include "wb.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "simp23.mm"
include "brcolinear.mm"
include "syl13anc.mm"
include "adantr.mm"
include "simp32.mm"
include "simp31.mm"
include "simp33.mm"
include "3imtr4d.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"

theorem colinearxfr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( B Colinear <. A , C >. /\ <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. ) -> E Colinear <. D , F >. ) )

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
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cB
    cA
    cC
    cop
    #
    ccolin
    wbr
    #
    cA
    cB
    cC
    cop
    cop
    cD
    cE
    cF
    cop
    cop
    ccgr3
    wbr
    #
    cE
    cD
    cF
    cop
    #
    ccolin
    wbr
    #
    @10
    @13
    @12
    @15
    @10
    @13
    @12
    @15
    wi
    @10
    @13
    wa
    #
    cB
    @11
    cbtwn
    wbr
    #
    cA
    cC
    cB
    cop
    cbtwn
    wbr
    #
    cC
    cB
    cA
    cop
    cbtwn
    wbr
    #
    w3o
    #
    cE
    @14
    cbtwn
    wbr
    #
    cD
    cF
    cE
    cop
    cbtwn
    wbr
    #
    cF
    cE
    cD
    cop
    cbtwn
    wbr
    #
    w3o
    #
    @12
    @15
    @16
    @17
    @21
    @18
    @22
    @19
    @23
    @10
    @13
    @17
    @21
    wi
    @10
    @17
    @13
    @21
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    btwnxfr
    expcomd
    imp
    @10
    @13
    @18
    @22
    wi
    #
    @10
    @13
    cC
    cA
    cB
    cop
    cop
    cF
    cD
    cE
    cop
    cop
    ccgr3
    wbr
    #
    @25
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    cgr3permute4
    @10
    @18
    @26
    @22
    @0
    @0
    @5
    @4
    @2
    @3
    w3a
    @9
    @8
    @6
    @7
    w3a
    @18
    @26
    wa
    @22
    wi
    @0
    biid
    #
    @4
    @2
    @3
    3anrot
    @8
    @6
    @7
    3anrot
    cC
    cA
    cB
    cF
    cD
    cE
    cN
    btwnxfr
    syl3anbr
    expcomd
    sylbid
    imp
    @10
    @13
    @19
    @23
    wi
    #
    @10
    @13
    cB
    cC
    cA
    cop
    cop
    cE
    cF
    cD
    cop
    cop
    ccgr3
    wbr
    #
    @28
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    cgr3permute3
    @10
    @19
    @29
    @23
    @0
    @0
    @5
    @3
    @4
    @2
    w3a
    @9
    @7
    @8
    @6
    w3a
    @19
    @29
    wa
    @23
    wi
    @27
    @2
    @3
    @4
    3anrot
    @6
    @7
    @8
    3anrot
    cB
    cC
    cA
    cE
    cF
    cD
    cN
    btwnxfr
    syl3anb
    expcomd
    sylbid
    imp
    3orim123d
    @10
    @12
    @20
    wb
    #
    @13
    @10
    @0
    @3
    @2
    @4
    @30
    @0
    @5
    @9
    simp1
    #
    @0
    @2
    @3
    @4
    @9
    simp22
    @0
    @2
    @3
    @4
    @9
    simp21
    @0
    @2
    @3
    @4
    @9
    simp23
    cB
    cA
    cC
    cN
    brcolinear
    syl13anc
    adantr
    @10
    @15
    @24
    wb
    #
    @13
    @10
    @0
    @7
    @6
    @8
    @32
    @31
    @0
    @5
    @6
    @7
    @8
    simp32
    @0
    @5
    @6
    @7
    @8
    simp31
    @0
    @5
    @6
    @7
    @8
    simp33
    cE
    cD
    cF
    cN
    brcolinear
    syl13anc
    adantr
    3imtr4d
    ex
    com23
    impd
end
