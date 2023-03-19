include "cc.mm"
include "cq.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wn.mm"
include "eldifn.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "cmin.mm"
include "cdiv.mm"
include "simpll1.mm"
include "eldifad.mm"
include "simp2r.mm"
include "ad2antrr.mm"
include "qcn.mm"
include "syl.mm"
include "simp3r.mm"
include "subdid.mm"
include "qsubcl.mm"
include "syl2anc.mm"
include "mulcomd.mm"
include "simplr.mm"
include "simp2l.mm"
include "mulcld.mm"
include "simp3l.mm"
include "addsubeq4d.mm"
include "mpbid.mm"
include "3eqtr4d.mm"
include "cc0.mm"
include "wne.mm"
include "simpr.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "divmuld.mm"
include "qdivcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "mt3d.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "simpl1.mm"
include "simpl3r.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "addcan2ad.mm"
include "jcai.mm"
include "ancomd.mm"
include "id.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "impbid1.mm"

theorem qirropth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( A e. ( CC \ QQ ) /\ ( B e. QQ /\ C e. QQ ) /\ ( D e. QQ /\ E e. QQ ) ) -> ( ( B + ( A x. C ) ) = ( D + ( A x. E ) ) <-> ( B = D /\ C = E ) ) )

  proof
    cA
    cc
    cq
    cdif
    wcel
    #
    cB
    cq
    wcel
    #
    cC
    cq
    wcel
    #
    wa
    #
    cD
    cq
    wcel
    #
    cE
    cq
    wcel
    #
    wa
    #
    w3a
    #
    cB
    cA
    cC
    cmul
    co
    #
    caddc
    co
    #
    cD
    cA
    cE
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    cB
    cD
    wceq
    #
    cC
    cE
    wceq
    #
    wa
    #
    @7
    @12
    @15
    @7
    @12
    wa
    #
    @14
    @13
    @16
    @14
    @13
    @16
    @14
    cA
    cq
    wcel
    #
    @7
    @17
    wn
    #
    @12
    @0
    @3
    @18
    @6
    cA
    cc
    cq
    eldifn
    3ad2ant1
    adantr
    @16
    @14
    wn
    #
    @17
    @16
    @19
    wa
    #
    cD
    cB
    cmin
    co
    #
    cC
    cE
    cmin
    co
    #
    cdiv
    co
    #
    cA
    cq
    @20
    @23
    cA
    wceq
    @22
    cA
    cmul
    co
    #
    @21
    wceq
    @20
    cA
    @22
    cmul
    co
    @8
    @10
    cmin
    co
    #
    @24
    @21
    @20
    cA
    cC
    cE
    @20
    cA
    cc
    cq
    @0
    @3
    @6
    @12
    @19
    simpll1
    eldifad
    #
    @20
    @2
    cC
    cc
    wcel
    #
    @7
    @2
    @12
    @19
    @0
    @1
    @2
    @6
    simp2r
    ad2antrr
    #
    cC
    qcn
    syl
    #
    @20
    @5
    cE
    cc
    wcel
    #
    @7
    @5
    @12
    @19
    @0
    @3
    @4
    @5
    simp3r
    ad2antrr
    #
    cE
    qcn
    #
    syl
    #
    subdid
    @20
    @22
    cA
    @20
    @22
    cq
    wcel
    #
    @22
    cc
    wcel
    @20
    @2
    @5
    @34
    @28
    @31
    cC
    cE
    qsubcl
    syl2anc
    #
    @22
    qcn
    syl
    #
    @26
    mulcomd
    @20
    @12
    @21
    @25
    wceq
    @7
    @12
    @19
    simplr
    @20
    cB
    @8
    cD
    @10
    @20
    @1
    cB
    cc
    wcel
    #
    @7
    @1
    @12
    @19
    @0
    @1
    @2
    @6
    simp2l
    ad2antrr
    #
    cB
    qcn
    #
    syl
    @20
    cA
    cC
    @26
    @29
    mulcld
    @20
    @4
    cD
    cc
    wcel
    #
    @7
    @4
    @12
    @19
    @0
    @3
    @4
    @5
    simp3l
    ad2antrr
    #
    cD
    qcn
    #
    syl
    @20
    cA
    cE
    @26
    @33
    mulcld
    addsubeq4d
    mpbid
    3eqtr4d
    @20
    @21
    @22
    cA
    @20
    @21
    cq
    wcel
    #
    @21
    cc
    wcel
    @20
    @4
    @1
    @43
    @41
    @38
    cD
    cB
    qsubcl
    syl2anc
    #
    @21
    qcn
    syl
    @36
    @26
    @20
    @22
    cc0
    wne
    #
    @19
    @16
    @19
    simpr
    @20
    @27
    @30
    @45
    @19
    wb
    @29
    @33
    @27
    @30
    wa
    @14
    @22
    cc0
    cC
    cE
    subeq0
    necon3abid
    syl2anc
    mpbird
    #
    divmuld
    mpbird
    @20
    @43
    @34
    @45
    @23
    cq
    wcel
    @44
    @35
    @46
    @21
    @22
    qdivcl
    syl3anc
    eqeltrrd
    ex
    mt3d
    @16
    @14
    @13
    @16
    @14
    wa
    #
    cB
    cD
    @10
    @16
    @37
    @14
    @16
    @1
    @37
    @1
    @2
    @0
    @6
    @12
    simpl2l
    @39
    syl
    adantr
    @16
    @40
    @14
    @16
    @4
    @40
    @4
    @5
    @0
    @3
    @12
    simpl3l
    @42
    syl
    adantr
    @16
    @10
    cc
    wcel
    @14
    @16
    cA
    cE
    @16
    cA
    cc
    cq
    @0
    @3
    @6
    @12
    simpl1
    eldifad
    @16
    @5
    @30
    @4
    @5
    @0
    @3
    @12
    simpl3r
    @32
    syl
    mulcld
    adantr
    @47
    cB
    @10
    caddc
    co
    @9
    @11
    @47
    @10
    @8
    cB
    caddc
    @47
    cE
    cC
    cA
    cmul
    @47
    cC
    cE
    @16
    @14
    simpr
    eqcomd
    oveq2d
    oveq2d
    @7
    @12
    @14
    simplr
    eqtrd
    addcan2ad
    ex
    jcai
    ancomd
    ex
    @13
    @14
    cB
    cD
    @8
    @10
    caddc
    @13
    id
    cC
    cE
    cA
    cmul
    oveq2
    oveqan12d
    impbid1
end
