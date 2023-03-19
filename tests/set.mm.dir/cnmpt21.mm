include "cmpt.mm"
include "cmpt2.mm"
include "ccom.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cxp.mm"
include "wral.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "df-ov.mm"
include "simprl.mm"
include "simprr.mm"
include "wi.mm"
include "wf.mm"
include "ctopon.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "rsp2.mm"
include "syl.mm"
include "imp.mm"
include "ovmpt4g.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "cuni.mm"
include "ctop.mm"
include "cntop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "fmpt.mm"
include "adantr.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "eqtrd.mm"
include "opelxpi.mm"
include "fvco3.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt21.mm"
include "nfco.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfral.mm"
include "nfmpt22.mm"
include "opeq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "opeq1.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "fveq2.mm"
include "ralxp.mm"
include "wfn.mm"
include "wb.mm"
include "fco.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "mpbird.mm"
include "cnco.mm"
include "eqeltrrd.mm"

theorem cnmpt21
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vw: setvar w
  let vu: setvar u
  let vv: setvar v
  let cD: class D
  let cF: class F
  let cN: class N
  let cP: class P
  let cW: class W
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt21.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )
  assume cnmpt21.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmpt21.b: |- ( ph -> ( z e. Z |-> B ) e. ( L Cn M ) )
  assume cnmpt21.c: |- ( z = A -> B = C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C z
  disjoint A z
  disjoint J z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint K z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint w z
  disjoint C w
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint C u
  disjoint C v
  disjoint D w
  disjoint D z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint v x
  disjoint v y
  disjoint L v
  disjoint L w
  disjoint ph v
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint M v
  disjoint M w
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
  disjoint K v
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  assert |- ( ph -> ( x e. X , y e. Y |-> C ) e. ( ( J tX K ) Cn M ) )

  proof
    wph
    vz
    cZ
    cB
    cmpt
    #
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    ccom
    #
    vx
    vy
    cX
    cY
    cC
    cmpt2
    #
    cJ
    cK
    ctx
    co
    #
    cM
    ccn
    co
    #
    wph
    @2
    @3
    wceq
    #
    vw
    cv
    #
    @2
    cfv
    #
    @7
    @3
    cfv
    #
    wceq
    #
    vw
    cX
    cY
    cxp
    #
    wral
    #
    wph
    vu
    cv
    #
    vv
    cv
    #
    cop
    #
    @2
    cfv
    #
    @15
    @3
    cfv
    #
    wceq
    #
    vv
    cY
    wral
    #
    vu
    cX
    wral
    #
    @12
    wph
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @2
    cfv
    #
    @23
    @3
    cfv
    #
    wceq
    #
    vy
    cY
    wral
    #
    vx
    cX
    wral
    @20
    wph
    @26
    vx
    vy
    cX
    cY
    wph
    @21
    cX
    wcel
    #
    @22
    cY
    wcel
    #
    wa
    #
    wa
    #
    @23
    @1
    cfv
    #
    @0
    cfv
    #
    cC
    @24
    @25
    @31
    @33
    cA
    @0
    cfv
    #
    cC
    @31
    @32
    cA
    @0
    @31
    @32
    @21
    @22
    @1
    co
    #
    cA
    @21
    @22
    @1
    df-ov
    @31
    @28
    @29
    cA
    cZ
    wcel
    #
    @35
    cA
    wceq
    wph
    @28
    @29
    simprl
    #
    wph
    @28
    @29
    simprr
    #
    wph
    @30
    @36
    wph
    @36
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @30
    @36
    wi
    wph
    @11
    cZ
    @1
    wf
    #
    @39
    wph
    @4
    @11
    ctopon
    cfv
    wcel
    #
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @1
    @4
    cL
    ccn
    co
    wcel
    #
    @40
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
    @41
    cnmpt21.j
    cnmpt21.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    cnmpt21.l
    cnmpt21.a
    @1
    @4
    cL
    @11
    cZ
    cnf2
    syl3anc
    #
    vx
    vy
    cX
    cY
    cA
    cZ
    @1
    @1
    eqid
    #
    fmpt2
    sylibr
    @36
    vx
    vy
    cX
    cY
    rsp2
    syl
    imp
    #
    vx
    vy
    cX
    cY
    cA
    @1
    cZ
    @45
    ovmpt4g
    syl3anc
    syl5eqr
    fveq2d
    @31
    @36
    cC
    cM
    cuni
    #
    wcel
    #
    @34
    cC
    wceq
    @46
    @31
    @36
    cB
    @47
    wcel
    #
    vz
    cZ
    wral
    #
    @48
    @46
    wph
    @50
    @30
    wph
    cZ
    @47
    @0
    wf
    #
    @50
    wph
    @42
    cM
    @47
    ctopon
    cfv
    wcel
    #
    @0
    cL
    cM
    ccn
    co
    wcel
    #
    @51
    cnmpt21.l
    wph
    cM
    ctop
    wcel
    #
    @52
    wph
    @53
    @54
    cnmpt21.b
    @0
    cL
    cM
    cntop2
    syl
    cM
    @47
    @47
    eqid
    toptopon
    sylib
    cnmpt21.b
    @0
    cL
    cM
    cZ
    @47
    cnf2
    syl3anc
    #
    vz
    cZ
    @47
    cB
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    adantr
    @49
    @48
    vz
    cA
    cZ
    vz
    cv
    cA
    wceq
    cB
    cC
    @47
    cnmpt21.c
    eleq1d
    rspcv
    sylc
    #
    vz
    cA
    cB
    cC
    cZ
    @47
    @0
    cnmpt21.c
    @56
    fvmptg
    syl2anc
    eqtrd
    wph
    @40
    @23
    @11
    wcel
    @24
    @33
    wceq
    @30
    @44
    @21
    @22
    cX
    cY
    opelxpi
    @11
    cZ
    @23
    @0
    @1
    fvco3
    syl2an
    @31
    @25
    @21
    @22
    @3
    co
    #
    cC
    @21
    @22
    @3
    df-ov
    @31
    @28
    @29
    @48
    @58
    cC
    wceq
    @37
    @38
    @57
    vx
    vy
    cX
    cY
    cC
    @3
    @47
    @3
    eqid
    #
    ovmpt4g
    syl3anc
    syl5eqr
    3eqtr4d
    ralrimivva
    @27
    @19
    vx
    vu
    cX
    @27
    vu
    nfv
    @18
    vx
    vv
    cY
    vx
    cY
    nfcv
    vx
    @16
    @17
    vx
    @15
    @2
    vx
    @0
    @1
    vx
    @0
    nfcv
    vx
    vy
    cX
    cY
    cA
    nfmpt21
    nfco
    vx
    @15
    nfcv
    #
    nffv
    vx
    @15
    @3
    vx
    vy
    cX
    cY
    cC
    nfmpt21
    @60
    nffv
    nfeq
    nfral
    @27
    @21
    @14
    cop
    #
    @2
    cfv
    #
    @61
    @3
    cfv
    #
    wceq
    #
    vv
    cY
    wral
    @21
    @13
    wceq
    #
    @19
    @26
    @64
    vy
    vv
    cY
    @26
    vv
    nfv
    vy
    @62
    @63
    vy
    @61
    @2
    vy
    @0
    @1
    vy
    @0
    nfcv
    vx
    vy
    cX
    cY
    cA
    nfmpt22
    nfco
    vy
    @61
    nfcv
    #
    nffv
    vy
    @61
    @3
    vx
    vy
    cX
    cY
    cC
    nfmpt22
    @66
    nffv
    nfeq
    @22
    @14
    wceq
    #
    @24
    @62
    @25
    @63
    @67
    @23
    @61
    @2
    @22
    @14
    @21
    opeq2
    #
    fveq2d
    @67
    @23
    @61
    @3
    @68
    fveq2d
    eqeq12d
    cbvral
    @65
    @64
    @18
    vv
    cY
    @65
    @62
    @16
    @63
    @17
    @65
    @61
    @15
    @2
    @21
    @13
    @14
    opeq1
    #
    fveq2d
    @65
    @61
    @15
    @3
    @69
    fveq2d
    eqeq12d
    ralbidv
    syl5bb
    cbvral
    sylib
    @10
    @18
    vw
    vu
    vv
    cX
    cY
    @7
    @15
    wceq
    @8
    @16
    @9
    @17
    @7
    @15
    @2
    fveq2
    @7
    @15
    @3
    fveq2
    eqeq12d
    ralxp
    sylibr
    wph
    @2
    @11
    wfn
    #
    @3
    @11
    wfn
    #
    @6
    @12
    wb
    wph
    @11
    @47
    @2
    wf
    #
    @70
    wph
    @51
    @40
    @72
    @55
    @44
    @11
    cZ
    @47
    @0
    @1
    fco
    syl2anc
    @11
    @47
    @2
    ffn
    syl
    wph
    @11
    @47
    @3
    wf
    #
    @71
    wph
    @48
    vy
    cY
    wral
    vx
    cX
    wral
    @73
    wph
    @48
    vx
    vy
    cX
    cY
    @57
    ralrimivva
    vx
    vy
    cX
    cY
    cC
    @47
    @3
    @59
    fmpt2
    sylib
    @11
    @47
    @3
    ffn
    syl
    vw
    @11
    @2
    @3
    eqfnfv
    syl2anc
    mpbird
    wph
    @43
    @53
    @2
    @5
    wcel
    cnmpt21.a
    cnmpt21.b
    @1
    @0
    @4
    cL
    cM
    cnco
    syl2anc
    eqeltrrd
end
