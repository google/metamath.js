include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wa.mm"
include "ccgr.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl31.mm"
include "cgrtriv.mm"
include "syl3anc.mm"
include "simprrl.mm"
include "wb.mm"
include "simpl23.mm"
include "simpl33.mm"
include "cgrcomlr.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "jca.mm"
include "wi.mm"
include "simpl22.mm"
include "simpl32.mm"
include "cifs.mm"
include "brifs.mm"
include "ifscgr.mm"
include "sylbird.mm"
include "syl333anc.mm"
include "mp3and.mm"
include "ex.mm"

theorem cgrsub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( ( B Btwn <. A , C >. /\ E Btwn <. D , F >. ) /\ ( <. A , C >. Cgr <. D , F >. /\ <. B , C >. Cgr <. E , F >. ) ) -> <. A , B >. Cgr <. D , E >. ) )

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
    cbtwn
    wbr
    cE
    cD
    cF
    cop
    #
    cbtwn
    wbr
    wa
    #
    @11
    @12
    ccgr
    wbr
    #
    cB
    cC
    cop
    cE
    cF
    cop
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cop
    #
    cD
    cE
    cop
    #
    ccgr
    wbr
    #
    @10
    @17
    wa
    #
    cB
    cA
    cop
    cE
    cD
    cop
    ccgr
    wbr
    #
    @20
    @21
    @13
    @16
    cA
    cA
    cop
    cD
    cD
    cop
    ccgr
    wbr
    #
    cC
    cA
    cop
    #
    cF
    cD
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    @22
    @10
    @13
    @16
    simprl
    @10
    @13
    @16
    simprr
    @21
    @23
    @26
    @21
    @0
    @2
    @6
    @23
    @0
    @5
    @9
    @17
    simpl1
    #
    @2
    @3
    @4
    @0
    @9
    @17
    simpl21
    #
    @6
    @7
    @8
    @0
    @5
    @17
    simpl31
    #
    cA
    cD
    cN
    cgrtriv
    syl3anc
    @21
    @14
    @26
    @10
    @13
    @14
    @15
    simprrl
    @21
    @0
    @2
    @4
    @6
    @8
    @14
    @26
    wb
    @28
    @29
    @2
    @3
    @4
    @0
    @9
    @17
    simpl23
    #
    @30
    @6
    @7
    @8
    @0
    @5
    @17
    simpl33
    #
    cA
    cC
    cD
    cF
    cN
    cgrcomlr
    syl122anc
    mpbid
    jca
    @21
    @0
    @2
    @3
    @4
    @2
    @6
    @7
    @8
    @6
    @13
    @16
    @27
    w3a
    #
    @22
    wi
    @28
    @29
    @2
    @3
    @4
    @0
    @9
    @17
    simpl22
    #
    @31
    @29
    @30
    @6
    @7
    @8
    @0
    @5
    @17
    simpl32
    #
    @32
    @30
    @0
    @2
    @3
    w3a
    @4
    @2
    @6
    w3a
    @7
    @8
    @6
    w3a
    w3a
    @33
    @18
    @24
    cop
    @19
    @25
    cop
    cifs
    wbr
    @22
    cA
    cB
    cC
    cA
    cD
    cE
    cF
    cD
    cN
    brifs
    cA
    cB
    cC
    cA
    cD
    cE
    cF
    cD
    cN
    ifscgr
    sylbird
    syl333anc
    mp3and
    @21
    @0
    @3
    @2
    @7
    @6
    @22
    @20
    wb
    @28
    @34
    @29
    @35
    @30
    cB
    cA
    cE
    cD
    cN
    cgrcomlr
    syl122anc
    mpbid
    ex
end
