include "con0.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wcel.mm"
include "wi.mm"
include "nfim.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "r19.21v.mm"
include "rsp.mm"
include "wss.mm"
include "onss.mm"
include "wb.mm"
include "tfr1.mm"
include "fvreseq.mm"
include "mpanl2.mm"
include "syl6bir.mm"
include "sylan2.mm"
include "ancoms.mm"
include "imp.mm"
include "adantr.mm"
include "tfr2.mm"
include "jctr.mm"
include "jcab.mm"
include "sylibr.mm"
include "eqeq12.mm"
include "syl6.mm"
include "adantl.mm"
include "mpbird.mm"
include "exp43.mm"
include "com4t.mm"
include "exp4a.mm"
include "pm2.43d.mm"
include "syl.mm"
include "com3l.mm"
include "impd.mm"
include "a2d.mm"
include "syl5bi.mm"
include "tfis2f.mm"
include "com12.mm"
include "ralrimi.mm"
include "eqfnfv.mm"
include "mpan2.mm"
include "biimpar.mm"
include "syldan.mm"

theorem tfr3
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vy: setvar y
  let cA: class A
  assume tfr.1: |- F = recs ( G )

  disjoint B x
  disjoint F x
  disjoint G x
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint G f
  disjoint G y
  assert |- ( ( B Fn On /\ A. x e. On ( B ` x ) = ( G ` ( B |` x ) ) ) -> B = F )

  proof
    cB
    con0
    wfn
    #
    vx
    cv
    #
    cB
    cfv
    #
    cB
    @1
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vx
    con0
    wral
    #
    @2
    @1
    cF
    cfv
    #
    wceq
    #
    vx
    con0
    wral
    #
    cB
    cF
    wceq
    #
    @0
    @6
    wa
    #
    @8
    vx
    con0
    @0
    @6
    vx
    @0
    vx
    nfv
    @5
    vx
    con0
    nfra1
    nfan
    #
    @1
    con0
    wcel
    #
    @11
    @8
    @11
    @8
    wi
    #
    @11
    vy
    cv
    #
    cB
    cfv
    #
    @15
    cF
    cfv
    #
    wceq
    #
    wi
    #
    vx
    vy
    @11
    @18
    vx
    @12
    @18
    vx
    nfv
    nfim
    @1
    @15
    wceq
    #
    @8
    @18
    @11
    @20
    @2
    @16
    @7
    @17
    @1
    @15
    cB
    fveq2
    @1
    @15
    cF
    fveq2
    eqeq12d
    imbi2d
    @19
    vy
    @1
    wral
    @11
    @18
    vy
    @1
    wral
    #
    wi
    @13
    @14
    @11
    @18
    vy
    @1
    r19.21v
    @13
    @11
    @21
    @8
    @13
    @0
    @6
    @21
    @8
    wi
    #
    @6
    @13
    @0
    @22
    @6
    @13
    @5
    wi
    #
    @13
    @0
    @22
    wi
    #
    wi
    @5
    vx
    con0
    rsp
    @23
    @13
    @24
    @23
    @13
    @13
    @0
    @22
    @13
    @0
    wa
    #
    @21
    @23
    @13
    @8
    @25
    @21
    @23
    @13
    @8
    @25
    @21
    wa
    #
    @23
    @13
    wa
    #
    wa
    @8
    @4
    cF
    @1
    cres
    #
    cG
    cfv
    #
    wceq
    #
    @26
    @30
    @27
    @25
    @21
    @30
    @0
    @13
    @21
    @30
    wi
    #
    @13
    @0
    @1
    con0
    wss
    #
    @31
    @1
    onss
    @0
    @32
    wa
    @21
    @3
    @28
    wceq
    #
    @30
    @0
    cF
    con0
    wfn
    #
    @32
    @33
    @21
    wb
    cF
    cG
    tfr.1
    tfr1
    #
    vy
    con0
    @1
    cB
    cF
    fvreseq
    mpanl2
    @3
    @28
    cG
    fveq2
    syl6bir
    sylan2
    ancoms
    imp
    adantr
    @27
    @8
    @30
    wb
    #
    @26
    @23
    @13
    @36
    @23
    @13
    @5
    @7
    @29
    wceq
    #
    wa
    #
    @36
    @23
    @23
    @13
    @37
    wi
    #
    wa
    @13
    @38
    wi
    @23
    @39
    @1
    cF
    cG
    tfr.1
    tfr2
    jctr
    @13
    @5
    @37
    jcab
    sylibr
    @2
    @4
    @7
    @29
    eqeq12
    syl6
    imp
    adantl
    mpbird
    exp43
    com4t
    exp4a
    pm2.43d
    syl
    com3l
    impd
    a2d
    syl5bi
    tfis2f
    com12
    ralrimi
    @0
    @10
    @9
    @0
    @34
    @10
    @9
    wb
    @35
    vx
    con0
    cB
    cF
    eqfnfv
    mpan2
    biimpar
    syldan
end
