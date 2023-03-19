include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "cabs.mm"
include "caddc.mm"
include "cneg.mm"
include "cmin.mm"
include "abscl.mm"
include "recnd.mm"
include "subneg.mm"
include "mpancom.mm"
include "eqeq1d.mm"
include "negcl.mm"
include "subeq0ad.mm"
include "bitr3d.mm"
include "wa.mm"
include "csqrt.mm"
include "ax-icn.mm"
include "cr.mm"
include "absge0.mm"
include "jca.mm"
include "eleq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "syl5ib.mm"
include "impcom.mm"
include "resqrtcl.mm"
include "syl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "sqrtneglem.mm"
include "negneg.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "3anbi1d.mm"
include "mpbid.mm"
include "oveq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "wb.mm"
include "oveq2.mm"
include "neleq1.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "sylbid.mm"
include "wne.mm"
include "cdiv.mm"
include "addcl.mm"
include "abs00ad.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "divcld.mm"
include "mulcld.mm"
include "eqid.mm"
include "sqreulem.mm"
include "pm2.61dne.mm"
include "sqrmo.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem sqreu
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. CC -> E! x e. CC ( ( x ^ 2 ) = A /\ 0 <_ ( Re ` x ) /\ ( _i x. x ) e/ RR+ ) )

  proof
    cA
    cc
    wcel
    #
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cc0
    @1
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @1
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    vx
    cc
    wrex
    #
    @8
    vx
    cc
    wrmo
    @8
    vx
    cc
    wreu
    @0
    @9
    cA
    cabs
    cfv
    #
    cA
    caddc
    co
    #
    cc0
    @0
    @11
    cc0
    wceq
    #
    @10
    cA
    cneg
    #
    wceq
    #
    @9
    @0
    @10
    @13
    cmin
    co
    #
    cc0
    wceq
    @12
    @14
    @0
    @15
    @11
    cc0
    @10
    cc
    wcel
    #
    @0
    @15
    @11
    wceq
    @0
    @10
    cA
    abscl
    #
    recnd
    #
    @10
    cA
    subneg
    mpancom
    eqeq1d
    @0
    @10
    @13
    @18
    cA
    negcl
    subeq0ad
    bitr3d
    @0
    @14
    @9
    @0
    @14
    wa
    #
    ci
    @13
    csqrt
    cfv
    #
    cmul
    co
    #
    cc
    wcel
    #
    @21
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cc0
    @21
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @21
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    @9
    @19
    ci
    cc
    wcel
    @20
    cc
    wcel
    @22
    ax-icn
    @19
    @20
    @19
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    wa
    #
    @20
    cr
    wcel
    @14
    @0
    @32
    @0
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    @14
    @32
    @0
    @33
    @34
    @17
    cA
    absge0
    #
    jca
    @14
    @33
    @30
    @34
    @31
    @10
    @13
    cr
    eleq1
    @10
    @13
    cc0
    cle
    breq2
    anbi12d
    syl5ib
    impcom
    #
    @13
    resqrtcl
    syl
    recnd
    ci
    @20
    mulcl
    sylancr
    @19
    @23
    @13
    cneg
    #
    wceq
    #
    @26
    @28
    w3a
    #
    @29
    @19
    @32
    @39
    @36
    @13
    sqrtneglem
    syl
    @19
    @38
    @24
    @26
    @28
    @19
    @37
    cA
    @23
    @0
    @37
    cA
    wceq
    @14
    cA
    negneg
    adantr
    eqeq2d
    3anbi1d
    mpbid
    @8
    @29
    vx
    @21
    cc
    @1
    @21
    wceq
    #
    @3
    @24
    @5
    @26
    @7
    @28
    @40
    @2
    @23
    cA
    @1
    @21
    c2
    cexp
    oveq1
    eqeq1d
    @40
    @4
    @25
    cc0
    cle
    @1
    @21
    cre
    fveq2
    breq2d
    @40
    @6
    @27
    wceq
    @7
    @28
    wb
    @1
    @21
    ci
    cmul
    oveq2
    @6
    @27
    crp
    neleq1
    syl
    3anbi123d
    rspcev
    syl2anc
    ex
    sylbid
    @0
    @11
    cc0
    wne
    #
    @9
    @0
    @41
    wa
    #
    @10
    csqrt
    cfv
    #
    @11
    @11
    cabs
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cc
    wcel
    @46
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cc0
    @46
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @46
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    @9
    @42
    @43
    @45
    @0
    @43
    cc
    wcel
    @41
    @0
    @43
    @0
    @33
    @34
    @43
    cr
    wcel
    @17
    @35
    @10
    resqrtcl
    syl2anc
    recnd
    adantr
    @42
    @11
    @44
    @0
    @11
    cc
    wcel
    #
    @41
    @16
    @0
    @54
    @18
    @10
    cA
    addcl
    mpancom
    #
    adantr
    @0
    @44
    cc
    wcel
    @41
    @0
    @44
    @0
    @54
    @44
    cr
    wcel
    @55
    @11
    abscl
    syl
    recnd
    adantr
    @0
    @44
    cc0
    wne
    @41
    @0
    @44
    cc0
    @11
    cc0
    @0
    @11
    @55
    abs00ad
    necon3bid
    biimpar
    divcld
    mulcld
    cA
    @46
    @46
    eqid
    sqreulem
    @8
    @53
    vx
    @46
    cc
    @1
    @46
    wceq
    #
    @3
    @48
    @5
    @50
    @7
    @52
    @56
    @2
    @47
    cA
    @1
    @46
    c2
    cexp
    oveq1
    eqeq1d
    @56
    @4
    @49
    cc0
    cle
    @1
    @46
    cre
    fveq2
    breq2d
    @56
    @6
    @51
    wceq
    @7
    @52
    wb
    @1
    @46
    ci
    cmul
    oveq2
    @6
    @51
    crp
    neleq1
    syl
    3anbi123d
    rspcev
    syl2anc
    ex
    pm2.61dne
    vx
    cA
    sqrmo
    @8
    vx
    cc
    reu5
    sylanbrc
end
