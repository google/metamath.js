include "ctx.mm"
include "co.mm"
include "cuni.mm"
include "cv.mm"
include "cmpt2.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "ccn.mm"
include "cxp.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "opeq12d.mm"
include "mpt2mpt.mm"
include "nfcv.mm"
include "nfmpt21.mm"
include "nfov.mm"
include "nfop.mm"
include "nfmpt22.mm"
include "wa.mm"
include "oveq12.mm"
include "cbvmpt2.mm"
include "eqtri.mm"
include "ctopon.mm"
include "wcel.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "toponuni.mm"
include "mpteq1.mm"
include "3syl.mm"
include "w3a.mm"
include "simp2.mm"
include "simp3.mm"
include "wral.mm"
include "wi.mm"
include "wf.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "rsp2.mm"
include "3impib.mm"
include "ovmpt4g.mm"
include "mpt2eq3dva.mm"
include "3eqtr3a.mm"
include "txcnmpt.mm"
include "eqeltrrd.mm"

theorem cnmpt2t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cF: class F
  let cN: class N
  let cP: class P
  let cW: class W
  let cZ: class Z
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt21.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )
  assume cnmpt2t.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( J tX K ) Cn M ) )

  disjoint x y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint M x
  disjoint M y
  disjoint Y x
  disjoint Y y
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint C u
  disjoint C v
  disjoint D w
  disjoint D z
  disjoint J v
  disjoint J z
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint v x
  disjoint v y
  disjoint L v
  disjoint L w
  disjoint L z
  disjoint ph v
  disjoint ph z
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint K v
  disjoint K z
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint B z
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( x e. X , y e. Y |-> <. A , B >. ) e. ( ( J tX K ) Cn ( L tX M ) ) )

  proof
    wph
    vz
    cJ
    cK
    ctx
    co
    #
    cuni
    #
    vz
    cv
    #
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    cfv
    #
    @2
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    cfv
    #
    cop
    #
    cmpt
    #
    vx
    vy
    cX
    cY
    cA
    cB
    cop
    #
    cmpt2
    #
    @0
    cL
    cM
    ctx
    co
    ccn
    co
    #
    wph
    vz
    cX
    cY
    cxp
    #
    @7
    cmpt
    #
    vx
    vy
    cX
    cY
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    @14
    @15
    @5
    co
    #
    cop
    #
    cmpt2
    #
    @8
    @10
    @13
    vu
    vv
    cX
    cY
    vu
    cv
    #
    vv
    cv
    #
    @3
    co
    #
    @20
    @21
    @5
    co
    #
    cop
    #
    cmpt2
    @19
    vu
    vv
    vz
    cX
    cY
    @7
    @24
    @2
    @20
    @21
    cop
    #
    wceq
    #
    @4
    @22
    @6
    @23
    @26
    @4
    @25
    @3
    cfv
    @22
    @2
    @25
    @3
    fveq2
    @20
    @21
    @3
    df-ov
    syl6eqr
    @26
    @6
    @25
    @5
    cfv
    @23
    @2
    @25
    @5
    fveq2
    @20
    @21
    @5
    df-ov
    syl6eqr
    opeq12d
    mpt2mpt
    vu
    vv
    vx
    vy
    cX
    cY
    @24
    @18
    vx
    @22
    @23
    vx
    @20
    @21
    @3
    vx
    @20
    nfcv
    #
    vx
    vy
    cX
    cY
    cA
    nfmpt21
    vx
    @21
    nfcv
    #
    nfov
    vx
    @20
    @21
    @5
    @27
    vx
    vy
    cX
    cY
    cB
    nfmpt21
    @28
    nfov
    nfop
    vy
    @22
    @23
    vy
    @20
    @21
    @3
    vy
    @20
    nfcv
    #
    vx
    vy
    cX
    cY
    cA
    nfmpt22
    vy
    @21
    nfcv
    #
    nfov
    vy
    @20
    @21
    @5
    @29
    vx
    vy
    cX
    cY
    cB
    nfmpt22
    @30
    nfov
    nfop
    vu
    @18
    nfcv
    vv
    @18
    nfcv
    @20
    @14
    wceq
    @21
    @15
    wceq
    wa
    @22
    @16
    @23
    @17
    @20
    @14
    @21
    @15
    @3
    oveq12
    @20
    @14
    @21
    @15
    @5
    oveq12
    opeq12d
    cbvmpt2
    eqtri
    wph
    @0
    @12
    ctopon
    cfv
    wcel
    #
    @12
    @1
    wceq
    @13
    @8
    wceq
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @31
    cnmpt21.j
    cnmpt21.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    #
    @12
    @0
    toponuni
    vz
    @12
    @1
    @7
    mpteq1
    3syl
    wph
    vx
    vy
    cX
    cY
    @18
    @9
    wph
    @14
    cX
    wcel
    #
    @15
    cY
    wcel
    #
    w3a
    #
    @16
    cA
    @17
    cB
    @35
    @33
    @34
    cA
    cL
    cuni
    #
    wcel
    #
    @16
    cA
    wceq
    wph
    @33
    @34
    simp2
    #
    wph
    @33
    @34
    simp3
    #
    wph
    @33
    @34
    @37
    wph
    @37
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @33
    @34
    wa
    #
    @37
    wi
    wph
    @12
    @36
    @3
    wf
    #
    @40
    wph
    @31
    cL
    @36
    ctopon
    cfv
    wcel
    #
    @3
    @0
    cL
    ccn
    co
    wcel
    #
    @42
    @32
    wph
    cL
    ctop
    wcel
    #
    @43
    wph
    @44
    @45
    cnmpt21.a
    @3
    @0
    cL
    cntop2
    syl
    cL
    @36
    @36
    eqid
    toptopon
    sylib
    cnmpt21.a
    @3
    @0
    cL
    @12
    @36
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cA
    @36
    @3
    @3
    eqid
    #
    fmpt2
    sylibr
    @37
    vx
    vy
    cX
    cY
    rsp2
    syl
    3impib
    vx
    vy
    cX
    cY
    cA
    @3
    @36
    @46
    ovmpt4g
    syl3anc
    @35
    @33
    @34
    cB
    cM
    cuni
    #
    wcel
    #
    @17
    cB
    wceq
    @38
    @39
    wph
    @33
    @34
    @48
    wph
    @48
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @41
    @48
    wi
    wph
    @12
    @47
    @5
    wf
    #
    @49
    wph
    @31
    cM
    @47
    ctopon
    cfv
    wcel
    #
    @5
    @0
    cM
    ccn
    co
    wcel
    #
    @50
    @32
    wph
    cM
    ctop
    wcel
    #
    @51
    wph
    @52
    @53
    cnmpt2t.b
    @5
    @0
    cM
    cntop2
    syl
    cM
    @47
    @47
    eqid
    toptopon
    sylib
    cnmpt2t.b
    @5
    @0
    cM
    @12
    @47
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cB
    @47
    @5
    @5
    eqid
    #
    fmpt2
    sylibr
    @48
    vx
    vy
    cX
    cY
    rsp2
    syl
    3impib
    vx
    vy
    cX
    cY
    cB
    @5
    @47
    @54
    ovmpt4g
    syl3anc
    opeq12d
    mpt2eq3dva
    3eqtr3a
    wph
    @44
    @52
    @8
    @11
    wcel
    cnmpt21.a
    cnmpt2t.b
    vz
    cL
    cM
    @0
    @3
    @5
    @8
    @1
    @1
    eqid
    @8
    eqid
    txcnmpt
    syl2anc
    eqeltrrd
end
