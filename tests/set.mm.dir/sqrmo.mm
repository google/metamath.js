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
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wrmo.mm"
include "wn.mm"
include "cneg.mm"
include "wo.mm"
include "simplr1.mm"
include "simprr1.mm"
include "eqtr4d.mm"
include "wb.mm"
include "sqeqor.mm"
include "ad2ant2r.mm"
include "mpbid.mm"
include "ord.mm"
include "3simpc.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "neleq1.mm"
include "syl.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "ad2antlr.mm"
include "syld.mm"
include "wne.mm"
include "negeq.mm"
include "neg0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "bitr4d.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "syli.mm"
include "cnpart.mm"
include "syl5ib.mm"
include "impancom.mm"
include "adantl.mm"
include "pm2.65d.mm"
include "notnotrd.mm"
include "an4s.mm"
include "ex.mm"
include "a1i.mm"
include "ralrimivv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem sqrmo
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. CC -> E* x e. CC ( ( x ^ 2 ) = A /\ 0 <_ ( Re ` x ) /\ ( _i x. x ) e/ RR+ ) )

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
    vy
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
    @9
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @9
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cc
    wral
    vx
    cc
    wral
    @8
    vx
    cc
    wrmo
    @0
    @19
    vx
    vy
    cc
    cc
    @1
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    wa
    #
    @19
    wi
    @0
    @22
    @17
    @18
    @20
    @8
    @21
    @16
    @18
    @20
    @8
    wa
    #
    @21
    @16
    wa
    #
    wa
    #
    @18
    @25
    @18
    wn
    #
    cc0
    @9
    cneg
    #
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @27
    cmul
    co
    #
    crp
    wnel
    #
    wa
    #
    @25
    @26
    @1
    @27
    wceq
    #
    @32
    @25
    @18
    @33
    @25
    @2
    @10
    wceq
    #
    @18
    @33
    wo
    #
    @25
    @2
    cA
    @10
    @3
    @5
    @7
    @20
    @24
    simplr1
    @11
    @13
    @15
    @21
    @23
    simprr1
    eqtr4d
    @20
    @21
    @34
    @35
    wb
    @8
    @16
    @1
    @9
    sqeqor
    ad2ant2r
    mpbid
    ord
    #
    @8
    @33
    @32
    wi
    @20
    @24
    @8
    @5
    @7
    wa
    @33
    @32
    @3
    @5
    @7
    3simpc
    @33
    @5
    @29
    @7
    @31
    @33
    @4
    @28
    cc0
    cle
    @1
    @27
    cre
    fveq2
    breq2d
    @33
    @6
    @30
    wceq
    @7
    @31
    wb
    @1
    @27
    ci
    cmul
    oveq2
    @6
    @30
    crp
    neleq1
    syl
    anbi12d
    syl5ibcom
    ad2antlr
    syld
    @25
    @26
    @9
    cc0
    wne
    #
    @32
    wn
    #
    @26
    @25
    @33
    @37
    @36
    @33
    @18
    @9
    cc0
    @9
    cc0
    wceq
    #
    @33
    @18
    @39
    @33
    @1
    cc0
    wceq
    @18
    @39
    @27
    cc0
    @1
    @39
    @27
    cc0
    cneg
    cc0
    @9
    cc0
    negeq
    neg0
    syl6eq
    eqeq2d
    @9
    cc0
    @1
    eqeq2
    bitr4d
    biimpcd
    necon3bd
    syli
    @24
    @37
    @38
    wi
    @23
    @21
    @37
    @16
    @38
    @16
    @13
    @15
    wa
    @21
    @37
    wa
    @38
    @11
    @13
    @15
    3simpc
    @9
    cnpart
    syl5ib
    impancom
    adantl
    syld
    pm2.65d
    notnotrd
    an4s
    ex
    a1i
    ralrimivv
    @8
    @16
    vx
    vy
    cc
    @18
    @3
    @11
    @5
    @13
    @7
    @15
    @18
    @2
    @10
    cA
    @1
    @9
    c2
    cexp
    oveq1
    eqeq1d
    @18
    @4
    @12
    cc0
    cle
    @1
    @9
    cre
    fveq2
    breq2d
    @18
    @6
    @14
    wceq
    @7
    @15
    wb
    @1
    @9
    ci
    cmul
    oveq2
    @6
    @14
    crp
    neleq1
    syl
    3anbi123d
    rmo4
    sylibr
end
