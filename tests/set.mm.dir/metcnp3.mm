include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "cbl.mm"
include "crn.mm"
include "wral.mm"
include "crp.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "3ad2ant1.mm"
include "ctg.mm"
include "wceq.mm"
include "mopnval.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "tgcnp.mm"
include "simpll2.mm"
include "simplr.mm"
include "simpll3.mm"
include "ffvelrnd.mm"
include "simpr.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "cxr.mm"
include "rpxr.mm"
include "adantl.mm"
include "blelrn.mm"
include "eleq2.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "simpl1.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "mopni2.mm"
include "sstr2.mm"
include "imass2.mm"
include "syl11.mm"
include "reximdv.mm"
include "syl5com.mm"
include "expimpd.mm"
include "expr.mm"
include "rexlimdv.mm"
include "syld.mm"
include "ralrimdva.mm"
include "simpl2.mm"
include "blss.mm"
include "3expib.mm"
include "r19.29r.mm"
include "ad3antrrr.mm"
include "ad2antrl.mm"
include "blopn.mm"
include "simprl.mm"
include "sstr.mm"
include "ad2ant2l.mm"
include "ancoms.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "expd.mm"
include "com23.mm"
include "exp4a.mm"
include "ralrimdv.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem metcnp3
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cZ: class Z
  let cA: class A
  let cB: class B
  let cE: class E
  let cL: class L
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )

  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J y
  disjoint J z
  disjoint K y
  disjoint K z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint P y
  disjoint P z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Z t
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint L t
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) /\ P e. X ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. RR+ E. z e. RR+ ( F " ( P ( ball ` C ) z ) ) C_ ( ( F ` P ) ( ball ` D ) y ) ) ) )

  proof
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cY
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    cX
    cY
    cF
    wf
    #
    cP
    cF
    cfv
    #
    vu
    cv
    #
    wcel
    #
    cP
    vv
    cv
    #
    wcel
    #
    cF
    @8
    cima
    #
    @6
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    wi
    #
    vu
    cD
    cbl
    cfv
    #
    crn
    #
    wral
    #
    wa
    @4
    cF
    cP
    vz
    cv
    #
    cC
    cbl
    cfv
    co
    #
    cima
    #
    @5
    vy
    cv
    #
    @15
    co
    #
    wss
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    @3
    vv
    vu
    @16
    cP
    cF
    cJ
    cK
    cX
    cY
    @0
    @1
    cJ
    cX
    ctopon
    cfv
    wcel
    @2
    cC
    cJ
    cX
    metcn.2
    mopntopon
    3ad2ant1
    @1
    @0
    cK
    @16
    ctg
    cfv
    wceq
    @2
    cD
    cK
    cY
    metcn.4
    mopnval
    3ad2ant2
    @1
    @0
    cK
    cY
    ctopon
    cfv
    wcel
    @2
    cD
    cK
    cY
    metcn.4
    mopntopon
    3ad2ant2
    @0
    @1
    @2
    simp3
    tgcnp
    @3
    @4
    @17
    @25
    @3
    @4
    wa
    #
    @17
    @25
    @26
    @17
    @24
    vy
    crp
    @26
    @21
    crp
    wcel
    #
    wa
    #
    @17
    @9
    @10
    @22
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    @24
    @28
    @17
    @5
    @22
    wcel
    #
    @31
    @28
    @1
    @5
    cY
    wcel
    #
    @27
    @32
    @0
    @1
    @2
    @4
    @27
    simpll2
    #
    @28
    cX
    cY
    cP
    cF
    @3
    @4
    @27
    simplr
    @0
    @1
    @2
    @4
    @27
    simpll3
    #
    ffvelrnd
    #
    @26
    @27
    simpr
    cD
    @5
    @21
    cY
    blcntr
    syl3anc
    @28
    @22
    @16
    wcel
    #
    @17
    @32
    @31
    wi
    #
    wi
    @28
    @1
    @33
    @21
    cxr
    wcel
    #
    @37
    @34
    @36
    @27
    @39
    @26
    @21
    rpxr
    adantl
    cD
    @5
    @21
    cY
    blelrn
    syl3anc
    @14
    @38
    vu
    @22
    @16
    @6
    @22
    wceq
    #
    @7
    @32
    @13
    @31
    @6
    @22
    @5
    eleq2
    @40
    @12
    @30
    vv
    cJ
    @40
    @11
    @29
    @9
    @6
    @22
    @10
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl
    mpid
    @28
    @30
    @24
    vv
    cJ
    @26
    @27
    @8
    cJ
    wcel
    #
    @30
    @24
    wi
    @26
    @27
    @41
    wa
    #
    wa
    #
    @9
    @29
    @24
    @43
    @9
    wa
    #
    @19
    @8
    wss
    #
    vz
    crp
    wrex
    #
    @29
    @24
    @44
    @0
    @41
    @9
    @46
    @26
    @0
    @42
    @9
    @0
    @1
    @2
    @4
    simpl1
    #
    ad2antrr
    @26
    @27
    @41
    @9
    simplrr
    @43
    @9
    simpr
    vz
    @8
    cC
    cP
    cJ
    cX
    metcn.2
    mopni2
    syl3anc
    @29
    @45
    @23
    vz
    crp
    @20
    @10
    wss
    @29
    @23
    @45
    @20
    @10
    @22
    sstr2
    @19
    @8
    cF
    imass2
    syl11
    reximdv
    syl5com
    expimpd
    expr
    rexlimdv
    syld
    ralrimdva
    @26
    @25
    @14
    vu
    @16
    @26
    @25
    @6
    @16
    wcel
    #
    @7
    @13
    @26
    @48
    @7
    wa
    #
    @25
    @13
    @26
    @49
    @22
    @6
    wss
    #
    vy
    crp
    wrex
    #
    @25
    @13
    wi
    @26
    @1
    @49
    @51
    wi
    @0
    @1
    @2
    @4
    simpl2
    @1
    @48
    @7
    @51
    vy
    @6
    cD
    @5
    cY
    blss
    3expib
    syl
    @26
    @51
    @25
    @13
    @51
    @25
    wa
    @50
    @24
    wa
    #
    vy
    crp
    wrex
    @26
    @13
    @50
    @24
    vy
    crp
    r19.29r
    @26
    @52
    @13
    vy
    crp
    @28
    @50
    @24
    @13
    @28
    @50
    wa
    #
    @23
    @13
    vz
    crp
    @53
    @18
    crp
    wcel
    #
    @23
    @13
    @53
    @54
    @23
    wa
    #
    wa
    #
    @19
    cJ
    wcel
    #
    cP
    @19
    wcel
    #
    @20
    @6
    wss
    #
    @13
    @56
    @0
    @2
    @18
    cxr
    wcel
    #
    @57
    @26
    @0
    @27
    @50
    @55
    @47
    ad3antrrr
    #
    @28
    @2
    @50
    @55
    @35
    ad2antrr
    #
    @54
    @60
    @53
    @23
    @18
    rpxr
    ad2antrl
    cC
    cP
    @18
    cJ
    cX
    metcn.2
    blopn
    syl3anc
    @56
    @0
    @2
    @54
    @58
    @61
    @62
    @53
    @54
    @23
    simprl
    cC
    cP
    @18
    cX
    blcntr
    syl3anc
    @55
    @53
    @59
    @23
    @50
    @59
    @54
    @28
    @20
    @22
    @6
    sstr
    ad2ant2l
    ancoms
    @12
    @58
    @59
    wa
    vv
    @19
    cJ
    @8
    @19
    wceq
    #
    @9
    @58
    @11
    @59
    @8
    @19
    cP
    eleq2
    @63
    @10
    @20
    @6
    @8
    @19
    cF
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    expr
    rexlimdva
    expimpd
    rexlimdva
    syl5
    expd
    syld
    com23
    exp4a
    ralrimdv
    impbid
    pm5.32da
    bitrd
end
