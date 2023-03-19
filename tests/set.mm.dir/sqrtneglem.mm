include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "ci.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cneg.mm"
include "wceq.mm"
include "cre.mm"
include "crp.mm"
include "wnel.mm"
include "c1.mm"
include "cc.mm"
include "ax-icn.mm"
include "resqrtcl.mm"
include "recn.mm"
include "syl.mm"
include "sqmul.mm"
include "sylancr.mm"
include "i2.mm"
include "a1i.mm"
include "resqrtth.mm"
include "oveq12d.mm"
include "adantr.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "renegcl.mm"
include "0re.mm"
include "cim.mm"
include "reim0.mm"
include "imre.mm"
include "eqtr3d.mm"
include "eqle.mm"
include "3syl.mm"
include "mul2neg.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "wn.mm"
include "ixi.mm"
include "oveq1i.mm"
include "mulass.mm"
include "mp3an12.mm"
include "mulm1.mm"
include "3eqtr3a.mm"
include "clt.mm"
include "sqrtge0.mm"
include "wb.mm"
include "le0neg2.mm"
include "lenlt.mm"
include "sylancl.mm"
include "bitrd.mm"
include "mpbid.mm"
include "biantrurd.mm"
include "elrp.mm"
include "syl6rbbr.mm"
include "mtbird.mm"
include "eqneltrd.mm"
include "df-nel.mm"
include "sylibr.mm"
include "3jca.mm"

theorem sqrtneglem
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( ( ( _i x. ( sqrt ` A ) ) ^ 2 ) = -u A /\ 0 <_ ( Re ` ( _i x. ( sqrt ` A ) ) ) /\ ( _i x. ( _i x. ( sqrt ` A ) ) ) e/ RR+ ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    ci
    cA
    csqrt
    cfv
    #
    cmul
    co
    #
    c2
    cexp
    co
    #
    cA
    cneg
    #
    wceq
    cc0
    @4
    cre
    cfv
    #
    cle
    wbr
    ci
    @4
    cmul
    co
    #
    crp
    wnel
    #
    @2
    @5
    ci
    c2
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    cmul
    co
    #
    c1
    cneg
    #
    cA
    cmul
    co
    @6
    @2
    ci
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @5
    @12
    wceq
    ax-icn
    @2
    @3
    cr
    wcel
    #
    @15
    cA
    resqrtcl
    #
    @3
    recn
    syl
    #
    ci
    @3
    sqmul
    sylancr
    @2
    @10
    @13
    @11
    cA
    cmul
    @10
    @13
    wceq
    @2
    i2
    a1i
    cA
    resqrtth
    oveq12d
    @2
    cA
    @0
    cA
    cc
    wcel
    @1
    cA
    recn
    adantr
    mulm1d
    3eqtrd
    @2
    cc0
    ci
    cneg
    @3
    cneg
    #
    cmul
    co
    #
    cre
    cfv
    #
    @7
    cle
    @2
    @16
    @19
    cr
    wcel
    #
    cc0
    @21
    cle
    wbr
    #
    @17
    @3
    renegcl
    #
    @22
    cc0
    cr
    wcel
    #
    cc0
    @21
    wceq
    @23
    0re
    @22
    @19
    cim
    cfv
    #
    cc0
    @21
    @19
    reim0
    @22
    @19
    cc
    wcel
    @26
    @21
    wceq
    @19
    recn
    @19
    imre
    syl
    eqtr3d
    cc0
    @21
    eqle
    sylancr
    3syl
    @2
    @20
    @4
    cre
    @2
    @14
    @15
    @20
    @4
    wceq
    ax-icn
    @18
    ci
    @3
    mul2neg
    sylancr
    fveq2d
    breqtrd
    @2
    @8
    crp
    wcel
    wn
    @9
    @2
    @8
    @19
    crp
    @2
    @15
    @8
    @19
    wceq
    @18
    @15
    ci
    ci
    cmul
    co
    #
    @3
    cmul
    co
    #
    @13
    @3
    cmul
    co
    @8
    @19
    @27
    @13
    @3
    cmul
    ixi
    oveq1i
    @14
    @14
    @15
    @28
    @8
    wceq
    ax-icn
    ax-icn
    ci
    ci
    @3
    mulass
    mp3an12
    @3
    mulm1
    3eqtr3a
    syl
    @2
    @19
    crp
    wcel
    #
    cc0
    @19
    clt
    wbr
    #
    @2
    cc0
    @3
    cle
    wbr
    #
    @30
    wn
    #
    cA
    sqrtge0
    @2
    @16
    @31
    @32
    wb
    @17
    @16
    @31
    @19
    cc0
    cle
    wbr
    #
    @32
    @3
    le0neg2
    @16
    @22
    @25
    @33
    @32
    wb
    @24
    0re
    @19
    cc0
    lenlt
    sylancl
    bitrd
    syl
    mpbid
    @2
    @30
    @22
    @30
    wa
    @29
    @2
    @22
    @30
    @2
    @16
    @22
    @17
    @24
    syl
    biantrurd
    @19
    elrp
    syl6rbbr
    mtbird
    eqneltrd
    @8
    crp
    df-nel
    sylibr
    3jca
end
