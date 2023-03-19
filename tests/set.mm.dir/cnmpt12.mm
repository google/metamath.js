include "cmpt2.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "wi.mm"
include "wal.mm"
include "jca.mm"
include "cxp.mm"
include "ctx.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "fmpt2.mm"
include "r2al.mm"
include "adantr.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "syl3c.mm"
include "ovmpt2ga.mm"
include "mpteq2dva.mm"
include "cnmpt12f.mm"
include "eqeltrrd.mm"

theorem cnmpt12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cF: class F
  let cP: class P
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt11.a: |- ( ph -> ( x e. X |-> A ) e. ( J Cn K ) )
  assume cnmpt1t.b: |- ( ph -> ( x e. X |-> B ) e. ( J Cn L ) )
  assume cnmpt12.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt12.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmpt12.c: |- ( ph -> ( y e. Y , z e. Z |-> C ) e. ( ( K tX L ) Cn M ) )
  assume cnmpt12.d: |- ( ( y = A /\ z = B ) -> C = D )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint ph x
  disjoint J x
  disjoint J y
  disjoint x z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint B y
  disjoint C x
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( x e. X |-> D ) e. ( J Cn M ) )

  proof
    wph
    vx
    cX
    cA
    cB
    vy
    vz
    cY
    cZ
    cC
    cmpt2
    #
    co
    #
    cmpt
    vx
    cX
    cD
    cmpt
    cJ
    cM
    ccn
    co
    wph
    vx
    cX
    @1
    cD
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    cA
    cY
    wcel
    #
    cB
    cZ
    wcel
    #
    cD
    cM
    cuni
    #
    wcel
    #
    @1
    cD
    wceq
    wph
    @4
    vx
    cX
    wph
    cX
    cY
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @4
    vx
    cX
    wral
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @8
    cJ
    cK
    ccn
    co
    wcel
    @9
    cnmptid.j
    cnmpt12.k
    cnmpt11.a
    @8
    cJ
    cK
    cX
    cY
    cnf2
    syl3anc
    vx
    cX
    cY
    cA
    @8
    @8
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    wph
    @5
    vx
    cX
    wph
    cX
    cZ
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @5
    vx
    cX
    wral
    wph
    @10
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @13
    cJ
    cL
    ccn
    co
    wcel
    @14
    cnmptid.j
    cnmpt12.l
    cnmpt1t.b
    @13
    cJ
    cL
    cX
    cZ
    cnf2
    syl3anc
    vx
    cX
    cZ
    cB
    @13
    @13
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    @3
    @4
    @5
    wa
    #
    vy
    cv
    #
    cY
    wcel
    #
    vz
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cC
    @6
    wcel
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    @17
    @7
    @3
    @4
    @5
    @12
    @16
    jca
    #
    wph
    @25
    @2
    wph
    @23
    vz
    cZ
    wral
    vy
    cY
    wral
    #
    @25
    wph
    cY
    cZ
    cxp
    #
    @6
    @0
    wf
    #
    @27
    wph
    cK
    cL
    ctx
    co
    #
    @28
    ctopon
    cfv
    wcel
    #
    cM
    @6
    ctopon
    cfv
    wcel
    #
    @0
    @30
    cM
    ccn
    co
    wcel
    #
    @29
    wph
    @11
    @15
    @31
    cnmpt12.k
    cnmpt12.l
    cK
    cL
    cY
    cZ
    txtopon
    syl2anc
    wph
    cM
    ctop
    wcel
    #
    @32
    wph
    @33
    @34
    cnmpt12.c
    @0
    @30
    cM
    cntop2
    syl
    cM
    @6
    @6
    eqid
    toptopon
    sylib
    cnmpt12.c
    @0
    @30
    cM
    @28
    @6
    cnf2
    syl3anc
    vy
    vz
    cY
    cZ
    cC
    @6
    @0
    @0
    eqid
    #
    fmpt2
    sylibr
    @23
    vy
    vz
    cY
    cZ
    r2al
    sylib
    adantr
    @26
    @24
    @17
    @7
    wi
    vy
    vz
    cA
    cB
    cY
    cZ
    @18
    cA
    wceq
    #
    @20
    cB
    wceq
    #
    wa
    #
    @22
    @17
    @23
    @7
    @36
    @19
    @4
    @37
    @21
    @5
    @18
    cA
    cY
    eleq1
    @20
    cB
    cZ
    eleq1
    bi2anan9
    @38
    cC
    cD
    @6
    cnmpt12.d
    eleq1d
    imbi12d
    spc2gv
    syl3c
    vy
    vz
    cA
    cB
    cY
    cZ
    cC
    cD
    @0
    @6
    cnmpt12.d
    @35
    ovmpt2ga
    syl3anc
    mpteq2dva
    wph
    vx
    cA
    cB
    @0
    cJ
    cK
    cL
    cM
    cX
    cnmptid.j
    cnmpt11.a
    cnmpt1t.b
    cnmpt12.c
    cnmpt12f
    eqeltrrd
end
