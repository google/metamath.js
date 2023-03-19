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
include "wi.mm"
include "wceq.mm"
include "wb.mm"
include "opeq1.mm"
include "breq1d.mm"
include "adantr.mm"
include "simp1.mm"
include "simp22.mm"
include "simp31.mm"
include "simp32.mm"
include "cgrid2.mm"
include "syl13anc.mm"
include "adantl.mm"
include "sylbid.mm"
include "breqan12d.mm"
include "exbiri.mm"
include "syld.mm"
include "impd.mm"
include "adantld.mm"
include "ex.mm"
include "wne.mm"
include "cofs.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "3jca.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpl33.mm"
include "simprrl.mm"
include "simprrr.mm"
include "cgrtriv.mm"
include "syl3anc.mm"
include "simpld.mm"
include "cgrcomlr.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "jca.mm"
include "brofs.mm"
include "syl333anc.mm"
include "mpbir3and.mm"
include "simprl.mm"
include "5segofs.mm"
include "sylc.mm"
include "exp32.mm"
include "com12.mm"
include "pm2.61ine.mm"

theorem cgrextend
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( ( B Btwn <. A , C >. /\ E Btwn <. D , F >. ) /\ ( <. A , B >. Cgr <. D , E >. /\ <. B , C >. Cgr <. E , F >. ) ) -> <. A , C >. Cgr <. D , F >. ) )

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
    cB
    cC
    cop
    #
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    @11
    @12
    ccgr
    wbr
    #
    wi
    #
    wi
    cA
    cB
    cA
    cB
    wceq
    #
    @10
    @23
    @24
    @10
    wa
    #
    @20
    @22
    @13
    @25
    @16
    @19
    @22
    @25
    @16
    cD
    cE
    wceq
    #
    @19
    @22
    wi
    #
    @25
    @16
    cB
    cB
    cop
    #
    @15
    ccgr
    wbr
    #
    @26
    @24
    @16
    @29
    wb
    @10
    @24
    @14
    @28
    @15
    ccgr
    cA
    cB
    cB
    opeq1
    breq1d
    adantr
    @10
    @29
    @26
    wi
    #
    @24
    @10
    @0
    @3
    @6
    @7
    @30
    @0
    @5
    @9
    simp1
    @0
    @2
    @3
    @4
    @9
    simp22
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
    simp32
    cB
    cD
    cE
    cN
    cgrid2
    syl13anc
    adantl
    sylbid
    @24
    @26
    @27
    wi
    @10
    @24
    @26
    @22
    @19
    @24
    @26
    @11
    @17
    @12
    @18
    ccgr
    cA
    cB
    cC
    opeq1
    cD
    cE
    cF
    opeq1
    breqan12d
    exbiri
    adantr
    syld
    impd
    adantld
    ex
    @10
    cA
    cB
    wne
    #
    @23
    @10
    @31
    @21
    @22
    @10
    @31
    @21
    wa
    #
    wa
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
    @22
    @33
    @0
    @2
    @3
    w3a
    #
    @4
    @2
    @6
    w3a
    #
    @7
    @8
    @6
    w3a
    #
    w3a
    @14
    @34
    cop
    @15
    @35
    cop
    cofs
    wbr
    #
    @31
    wa
    @36
    @33
    @37
    @38
    @39
    @33
    @0
    @2
    @3
    @0
    @5
    @9
    @32
    simpl1
    #
    @2
    @3
    @4
    @0
    @9
    @32
    simpl21
    #
    @2
    @3
    @4
    @0
    @9
    @32
    simpl22
    #
    3jca
    @33
    @4
    @2
    @6
    @2
    @3
    @4
    @0
    @9
    @32
    simpl23
    #
    @42
    @6
    @7
    @8
    @0
    @5
    @32
    simpl31
    #
    3jca
    @33
    @7
    @8
    @6
    @6
    @7
    @8
    @0
    @5
    @32
    simpl32
    #
    @6
    @7
    @8
    @0
    @5
    @32
    simpl33
    #
    @45
    3jca
    3jca
    @33
    @40
    @31
    @33
    @40
    @13
    @20
    cA
    cA
    cop
    cD
    cD
    cop
    ccgr
    wbr
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
    wa
    #
    @10
    @31
    @13
    @20
    simprrl
    @10
    @31
    @13
    @20
    simprrr
    #
    @33
    @48
    @49
    @33
    @0
    @2
    @6
    @48
    @41
    @42
    @45
    cA
    cD
    cN
    cgrtriv
    syl3anc
    @33
    @16
    @49
    @33
    @16
    @19
    @51
    simpld
    @33
    @0
    @2
    @3
    @6
    @7
    @16
    @49
    wb
    @41
    @42
    @43
    @45
    @46
    cA
    cB
    cD
    cE
    cN
    cgrcomlr
    syl122anc
    mpbid
    jca
    @33
    @0
    @2
    @3
    @4
    @2
    @6
    @7
    @8
    @6
    @40
    @13
    @20
    @50
    w3a
    wb
    @41
    @42
    @43
    @44
    @42
    @45
    @46
    @47
    @45
    cA
    cB
    cC
    cA
    cD
    cE
    cF
    cD
    cN
    brofs
    syl333anc
    mpbir3and
    @10
    @31
    @21
    simprl
    jca
    cA
    cB
    cC
    cA
    cD
    cE
    cF
    cD
    cN
    5segofs
    sylc
    @33
    @0
    @4
    @2
    @8
    @6
    @36
    @22
    wb
    @41
    @44
    @42
    @47
    @45
    cC
    cA
    cF
    cD
    cN
    cgrcomlr
    syl122anc
    mpbid
    exp32
    com12
    pm2.61ine
end
