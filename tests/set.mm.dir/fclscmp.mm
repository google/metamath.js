include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccmp.mm"
include "cv.mm"
include "cfcls.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cfil.mm"
include "wral.mm"
include "cuni.mm"
include "eqid.mm"
include "fclscmpi.mm"
include "ralrimiva.mm"
include "toponuni.mm"
include "fveq2d.mm"
include "raleqdv.mm"
include "syl5ibr.mm"
include "cfi.mm"
include "wn.mm"
include "cint.mm"
include "wi.mm"
include "ccld.mm"
include "cpw.mm"
include "wa.mm"
include "wss.mm"
include "elpwi.mm"
include "wceq.mm"
include "cvv.mm"
include "vn0.mm"
include "simpr.mm"
include "inteqd.mm"
include "int0.mm"
include "syl6eq.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "a1d.mm"
include "cfg.mm"
include "ccl.mm"
include "vex.mm"
include "ssfii.mm"
include "ax-mp.mm"
include "cfbas.mm"
include "simplrl.mm"
include "cldss2.mm"
include "ad2antrr.mm"
include "pweqd.mm"
include "syl5sseqr.mm"
include "sstrd.mm"
include "simplrr.mm"
include "w3a.mm"
include "wb.mm"
include "toponmax.mm"
include "fsubbas.mm"
include "syl.mm"
include "mpbir3and.mm"
include "ssfg.mm"
include "syl5ss.mm"
include "sselda.mm"
include "fclssscls.mm"
include "cldcls.mm"
include "sseqtrd.mm"
include "ssint.mm"
include "sylibr.mm"
include "fgcl.mm"
include "oveq2.mm"
include "rspcv.mm"
include "3syl.mm"
include "ssn0.mm"
include "syl6an.mm"
include "pm2.61dane.mm"
include "expr.mm"
include "sylan2.mm"
include "com23.mm"
include "ralrimdva.mm"
include "ctop.mm"
include "topontop.mm"
include "cmpfi.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem fclscmp
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vn: setvar n
  let vo: setvar o
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vy: setvar y
  let cL: class L
  let cN: class N
  let cF: class F
  let cY: class Y
  let cS: class S

  disjoint J f
  disjoint X f
  disjoint n o
  disjoint n x
  disjoint A n
  disjoint o x
  disjoint A o
  disjoint A x
  disjoint f g
  disjoint f j
  disjoint f n
  disjoint f o
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint g j
  disjoint g n
  disjoint g o
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j n
  disjoint j o
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n s
  disjoint n y
  disjoint J n
  disjoint o s
  disjoint o y
  disjoint J o
  disjoint s x
  disjoint s y
  disjoint J s
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint L f
  disjoint L g
  disjoint L j
  disjoint L n
  disjoint L o
  disjoint L s
  disjoint L x
  disjoint N n
  disjoint N s
  disjoint F f
  disjoint F g
  disjoint F n
  disjoint F o
  disjoint F s
  disjoint F x
  disjoint X g
  disjoint X j
  disjoint X n
  disjoint X o
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y j
  disjoint Y n
  disjoint Y o
  disjoint Y s
  disjoint Y x
  disjoint S s
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Comp <-> A. f e. ( Fil ` X ) ( J fClus f ) =/= (/) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ccmp
    wcel
    #
    cJ
    vf
    cv
    #
    cfcls
    co
    #
    c0
    wne
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    @1
    @6
    @0
    @4
    vf
    cJ
    cuni
    #
    cfil
    cfv
    #
    wral
    @1
    @4
    vf
    @8
    @2
    cJ
    @7
    @7
    eqid
    #
    fclscmpi
    ralrimiva
    @0
    @4
    vf
    @5
    @8
    @0
    cX
    @7
    cfil
    cX
    cJ
    toponuni
    #
    fveq2d
    raleqdv
    syl5ibr
    @0
    @6
    c0
    vx
    cv
    #
    cfi
    cfv
    #
    wcel
    wn
    #
    @11
    cint
    #
    c0
    wne
    #
    wi
    #
    vx
    cJ
    ccld
    cfv
    #
    cpw
    #
    wral
    #
    @1
    @0
    @6
    @16
    vx
    @18
    @0
    @11
    @18
    wcel
    #
    wa
    @13
    @6
    @15
    @20
    @0
    @11
    @17
    wss
    #
    @13
    @6
    @15
    wi
    #
    wi
    @11
    @17
    elpwi
    @0
    @21
    @13
    @22
    @0
    @21
    @13
    wa
    #
    wa
    #
    @22
    @11
    c0
    @24
    @11
    c0
    wceq
    #
    wa
    #
    @15
    @6
    @26
    @15
    cvv
    c0
    wne
    vn0
    @26
    @14
    cvv
    c0
    @26
    @14
    c0
    cint
    cvv
    @26
    @11
    c0
    @24
    @25
    simpr
    inteqd
    int0
    syl6eq
    neeq1d
    mpbiri
    a1d
    @24
    @11
    c0
    wne
    #
    wa
    #
    cJ
    cX
    @12
    cfg
    co
    #
    cfcls
    co
    #
    @14
    wss
    #
    @6
    @30
    c0
    wne
    #
    @15
    @28
    @30
    vy
    cv
    #
    wss
    #
    vy
    @11
    wral
    @31
    @28
    @34
    vy
    @11
    @28
    @33
    @11
    wcel
    wa
    #
    @30
    @33
    cJ
    ccl
    cfv
    cfv
    #
    @33
    @35
    @33
    @29
    wcel
    @30
    @36
    wss
    @28
    @11
    @29
    @33
    @28
    @11
    @12
    @29
    @11
    cvv
    wcel
    @11
    @12
    wss
    vx
    vex
    @11
    cvv
    ssfii
    ax-mp
    @28
    @12
    cX
    cfbas
    cfv
    wcel
    #
    @12
    @29
    wss
    @28
    @37
    @11
    cX
    cpw
    #
    wss
    #
    @27
    @13
    @28
    @11
    @17
    @38
    @0
    @21
    @13
    @27
    simplrl
    #
    @28
    @7
    cpw
    @17
    @38
    cJ
    @7
    @9
    cldss2
    @28
    cX
    @7
    @0
    cX
    @7
    wceq
    @23
    @27
    @10
    ad2antrr
    pweqd
    syl5sseqr
    sstrd
    @24
    @27
    simpr
    @0
    @21
    @13
    @27
    simplrr
    @28
    cX
    cJ
    wcel
    #
    @37
    @39
    @27
    @13
    w3a
    wb
    @0
    @41
    @23
    @27
    cX
    cJ
    toponmax
    ad2antrr
    @11
    cJ
    cX
    fsubbas
    syl
    mpbir3and
    #
    @12
    cX
    ssfg
    syl
    syl5ss
    sselda
    @33
    @29
    cJ
    fclssscls
    syl
    @35
    @33
    @17
    wcel
    @36
    @33
    wceq
    @28
    @11
    @17
    @33
    @40
    sselda
    @33
    cJ
    cldcls
    syl
    sseqtrd
    ralrimiva
    vy
    @30
    @11
    ssint
    sylibr
    @28
    @37
    @29
    @5
    wcel
    @6
    @32
    wi
    @42
    @12
    cX
    fgcl
    @4
    @32
    vf
    @29
    @5
    @2
    @29
    wceq
    @3
    @30
    c0
    @2
    @29
    cJ
    cfcls
    oveq2
    neeq1d
    rspcv
    3syl
    @30
    @14
    ssn0
    syl6an
    pm2.61dane
    expr
    sylan2
    com23
    ralrimdva
    @0
    cJ
    ctop
    wcel
    @1
    @19
    wb
    cX
    cJ
    topontop
    vx
    cJ
    cmpfi
    syl
    sylibrd
    impbid
end
