include "cop.mm"
include "cmpt2.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "df-ov.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "cxp.mm"
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
include "3impib.mm"
include "wal.mm"
include "jca.mm"
include "ctop.mm"
include "cntop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "r2al.mm"
include "3ad2ant1.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "syl3c.mm"
include "ovmpt2ga.mm"
include "syl5eqr.mm"
include "mpt2eq3dva.mm"
include "cnmpt2t.mm"
include "cnmpt21f.mm"
include "eqeltrrd.mm"

theorem cnmpt22
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let cF: class F
  let cP: class P
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt21.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )
  assume cnmpt2t.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( J tX K ) Cn M ) )
  assume cnmpt22.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmpt22.m: |- ( ph -> M e. ( TopOn ` W ) )
  assume cnmpt22.c: |- ( ph -> ( z e. Z , w e. W |-> C ) e. ( ( L tX M ) Cn N ) )
  assume cnmpt22.d: |- ( ( z = A /\ w = B ) -> C = D )

  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint D w
  disjoint D z
  disjoint J z
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint K z
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v z
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  disjoint J v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint v x
  disjoint v y
  disjoint L v
  disjoint ph v
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint X v
  disjoint M v
  disjoint N v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Y u
  disjoint Y v
  disjoint K v
  disjoint W v
  disjoint Z u
  disjoint Z v
  assert |- ( ph -> ( x e. X , y e. Y |-> D ) e. ( ( J tX K ) Cn N ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cA
    cB
    cop
    #
    vz
    vw
    cZ
    cW
    cC
    cmpt2
    #
    cfv
    #
    cmpt2
    vx
    vy
    cX
    cY
    cD
    cmpt2
    cJ
    cK
    ctx
    co
    #
    cN
    ccn
    co
    wph
    vx
    vy
    cX
    cY
    @2
    cD
    wph
    vx
    cv
    cX
    wcel
    #
    vy
    cv
    cY
    wcel
    #
    w3a
    #
    @2
    cA
    cB
    @1
    co
    #
    cD
    cA
    cB
    @1
    df-ov
    @6
    cA
    cZ
    wcel
    #
    cB
    cW
    wcel
    #
    cD
    cN
    cuni
    #
    wcel
    #
    @7
    cD
    wceq
    wph
    @4
    @5
    @8
    wph
    @8
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @4
    @5
    wa
    #
    @8
    wi
    wph
    cX
    cY
    cxp
    #
    cZ
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    wf
    #
    @12
    wph
    @3
    @14
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
    @15
    @3
    cL
    ccn
    co
    wcel
    @16
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
    @17
    cnmpt21.j
    cnmpt21.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    #
    cnmpt22.l
    cnmpt21.a
    @15
    @3
    cL
    @14
    cZ
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cA
    cZ
    @15
    @15
    eqid
    fmpt2
    sylibr
    @8
    vx
    vy
    cX
    cY
    rsp2
    syl
    3impib
    #
    wph
    @4
    @5
    @9
    wph
    @9
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @13
    @9
    wi
    wph
    @14
    cW
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    wf
    #
    @21
    wph
    @17
    cM
    cW
    ctopon
    cfv
    wcel
    #
    @22
    @3
    cM
    ccn
    co
    wcel
    @23
    @19
    cnmpt22.m
    cnmpt2t.b
    @22
    @3
    cM
    @14
    cW
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cB
    cW
    @22
    @22
    eqid
    fmpt2
    sylibr
    @9
    vx
    vy
    cX
    cY
    rsp2
    syl
    3impib
    #
    @6
    @8
    @9
    wa
    #
    vz
    cv
    #
    cZ
    wcel
    #
    vw
    cv
    #
    cW
    wcel
    #
    wa
    #
    cC
    @10
    wcel
    #
    wi
    #
    vw
    wal
    vz
    wal
    #
    @26
    @11
    @6
    @8
    @9
    @20
    @25
    jca
    #
    wph
    @4
    @34
    @5
    wph
    @32
    vw
    cW
    wral
    vz
    cZ
    wral
    #
    @34
    wph
    cZ
    cW
    cxp
    #
    @10
    @1
    wf
    #
    @36
    wph
    cL
    cM
    ctx
    co
    #
    @37
    ctopon
    cfv
    wcel
    #
    cN
    @10
    ctopon
    cfv
    wcel
    #
    @1
    @39
    cN
    ccn
    co
    wcel
    #
    @38
    wph
    @18
    @24
    @40
    cnmpt22.l
    cnmpt22.m
    cL
    cM
    cZ
    cW
    txtopon
    syl2anc
    wph
    cN
    ctop
    wcel
    #
    @41
    wph
    @42
    @43
    cnmpt22.c
    @1
    @39
    cN
    cntop2
    syl
    cN
    @10
    @10
    eqid
    toptopon
    sylib
    cnmpt22.c
    @1
    @39
    cN
    @37
    @10
    cnf2
    syl3anc
    vz
    vw
    cZ
    cW
    cC
    @10
    @1
    @1
    eqid
    #
    fmpt2
    sylibr
    @32
    vz
    vw
    cZ
    cW
    r2al
    sylib
    3ad2ant1
    @35
    @33
    @26
    @11
    wi
    vz
    vw
    cA
    cB
    cZ
    cW
    @27
    cA
    wceq
    #
    @29
    cB
    wceq
    #
    wa
    #
    @31
    @26
    @32
    @11
    @45
    @28
    @8
    @46
    @30
    @9
    @27
    cA
    cZ
    eleq1
    @29
    cB
    cW
    eleq1
    bi2anan9
    @47
    cC
    cD
    @10
    cnmpt22.d
    eleq1d
    imbi12d
    spc2gv
    syl3c
    vz
    vw
    cA
    cB
    cZ
    cW
    cC
    cD
    @1
    @10
    cnmpt22.d
    @44
    ovmpt2ga
    syl3anc
    syl5eqr
    mpt2eq3dva
    wph
    vx
    vy
    @0
    @1
    cJ
    cK
    @39
    cN
    cX
    cY
    cnmpt21.j
    cnmpt21.k
    wph
    vx
    vy
    cA
    cB
    cJ
    cK
    cL
    cM
    cX
    cY
    cnmpt21.j
    cnmpt21.k
    cnmpt21.a
    cnmpt2t.b
    cnmpt2t
    cnmpt22.c
    cnmpt21f
    eqeltrrd
end
