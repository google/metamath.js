include "cz.mm"
include "wcel.mm"
include "cneg.mm"
include "cn.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cnumer.mm"
include "cfv.mm"
include "cgcd.mm"
include "wceq.mm"
include "cdenom.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "zssq.mm"
include "simp1.mm"
include "sseldi.mm"
include "simp2.mm"
include "nnne0.mm"
include "3ad2ant3.mm"
include "neg0.mm"
include "neeq2i.mm"
include "sylibr.mm"
include "neneqd.mm"
include "zcnd.mm"
include "0cnd.mm"
include "neg11ad.mm"
include "mtbid.mm"
include "neqned.mm"
include "qdivcl.mm"
include "syl3anc.mm"
include "qnumcl.mm"
include "syl.mm"
include "cc.mm"
include "wa.mm"
include "simpl.mm"
include "3adant2.mm"
include "gcdcld.mm"
include "nn0cnd.mm"
include "negcld.mm"
include "wn.mm"
include "intnand.mm"
include "wb.mm"
include "gcdeq0.mm"
include "necon3abid.mm"
include "3adant3.mm"
include "mpbird.mm"
include "negne0d.mm"
include "divcld.mm"
include "divneg2d.mm"
include "fveq2d.mm"
include "numdenneg.mm"
include "simpld.mm"
include "gcdneg.mm"
include "oveq2d.mm"
include "divnumden.mm"
include "divnegd.mm"
include "div2negd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"
include "neg11d.mm"
include "eqtr4d.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "jca.mm"

theorem divnumden2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ -u B e. NN ) -> ( ( numer ` ( A / B ) ) = -u ( A / ( A gcd B ) ) /\ ( denom ` ( A / B ) ) = -u ( B / ( A gcd B ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cB
    cneg
    #
    cn
    wcel
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    cnumer
    cfv
    #
    cA
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    #
    cneg
    #
    wceq
    @5
    cdenom
    cfv
    #
    cB
    @7
    cdiv
    co
    cneg
    #
    wceq
    @4
    @6
    cA
    @7
    cneg
    #
    cdiv
    co
    #
    @9
    @4
    @6
    @13
    @4
    @6
    @4
    @5
    cq
    wcel
    #
    @6
    cz
    wcel
    @4
    cA
    cq
    wcel
    cB
    cq
    wcel
    cB
    cc0
    wne
    @14
    @4
    cz
    cq
    cA
    zssq
    @0
    @1
    @3
    simp1
    #
    sseldi
    @4
    cz
    cq
    cB
    zssq
    @0
    @1
    @3
    simp2
    #
    sseldi
    @4
    cB
    cc0
    @4
    @2
    cc0
    cneg
    #
    wceq
    cB
    cc0
    wceq
    #
    @4
    @2
    @17
    @4
    @2
    cc0
    wne
    #
    @2
    @17
    wne
    @3
    @0
    @19
    @1
    @2
    nnne0
    3ad2ant3
    @17
    cc0
    @2
    neg0
    neeq2i
    sylibr
    neneqd
    @4
    cB
    cc0
    @4
    cB
    @16
    zcnd
    #
    @4
    0cnd
    neg11ad
    mtbid
    #
    neqned
    #
    cA
    cB
    qdivcl
    syl3anc
    #
    @5
    qnumcl
    syl
    zcnd
    @4
    cA
    @12
    @0
    @3
    cA
    cc
    wcel
    @1
    @0
    @3
    wa
    #
    cA
    @0
    @3
    simpl
    zcnd
    3adant2
    #
    @4
    @7
    @4
    @7
    @4
    cA
    cB
    @15
    @16
    gcdcld
    nn0cnd
    #
    negcld
    #
    @4
    @7
    @26
    @4
    @7
    cc0
    wne
    #
    cA
    cc0
    wceq
    #
    @18
    wa
    #
    wn
    #
    @4
    @18
    @29
    @21
    intnand
    @0
    @1
    @28
    @31
    wb
    @3
    @0
    @1
    wa
    @30
    @7
    cc0
    cA
    cB
    gcdeq0
    necon3abid
    3adant3
    mpbird
    #
    negne0d
    #
    divcld
    @4
    @5
    cneg
    #
    cnumer
    cfv
    #
    cA
    @2
    cdiv
    co
    #
    cnumer
    cfv
    #
    @6
    cneg
    #
    @13
    cneg
    #
    @4
    @34
    @36
    cnumer
    @4
    cA
    cB
    @25
    @20
    @22
    divneg2d
    #
    fveq2d
    @4
    @14
    @35
    @38
    wceq
    #
    @23
    @14
    @41
    @34
    cdenom
    cfv
    #
    @10
    wceq
    #
    @5
    numdenneg
    #
    simpld
    syl
    @4
    cA
    cA
    @2
    cgcd
    co
    #
    cdiv
    co
    #
    @8
    @37
    @39
    @4
    @45
    @7
    cA
    cdiv
    @0
    @1
    @45
    @7
    wceq
    @3
    cA
    cB
    gcdneg
    3adant3
    #
    oveq2d
    @0
    @3
    @37
    @46
    wceq
    #
    @1
    @24
    @48
    @36
    cdenom
    cfv
    #
    @2
    @45
    cdiv
    co
    #
    wceq
    #
    cA
    @2
    divnumden
    #
    simpld
    3adant2
    @4
    @39
    cA
    cneg
    @12
    cdiv
    co
    @8
    @4
    cA
    @12
    @25
    @27
    @33
    divnegd
    @4
    cA
    @7
    @25
    @26
    @32
    div2negd
    eqtrd
    3eqtr4d
    3eqtr3d
    neg11d
    @4
    cA
    @7
    @25
    @26
    @32
    divneg2d
    eqtr4d
    @4
    @10
    cB
    @12
    cdiv
    co
    #
    @11
    @4
    @42
    @49
    @10
    @53
    @4
    @34
    @36
    cdenom
    @40
    fveq2d
    @4
    @14
    @43
    @23
    @14
    @41
    @43
    @44
    simprd
    syl
    @4
    @50
    @2
    @7
    cdiv
    co
    #
    @49
    @53
    @4
    @45
    @7
    @2
    cdiv
    @47
    oveq2d
    @0
    @3
    @51
    @1
    @24
    @48
    @51
    @52
    simprd
    3adant2
    @4
    @11
    @53
    @54
    @4
    cB
    @7
    @20
    @26
    @32
    divneg2d
    #
    @4
    cB
    @7
    @20
    @26
    @32
    divnegd
    eqtr3d
    3eqtr4d
    3eqtr3d
    @55
    eqtr4d
    jca
end
