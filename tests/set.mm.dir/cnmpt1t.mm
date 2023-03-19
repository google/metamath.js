include "cuni.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cop.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ctopon.mm"
include "wcel.mm"
include "wceq.mm"
include "toponuni.mm"
include "mpteq1.mm"
include "3syl.mm"
include "wa.mm"
include "simpr.mm"
include "wf.mm"
include "wral.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "opeq12d.mm"
include "mpteq2dva.mm"
include "eqtr3d.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfop.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "txcnmpt.mm"
include "eqeltrrd.mm"

theorem cnmpt1t
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cF: class F
  let cM: class M
  let cY: class Y
  let cZ: class Z
  let cP: class P
  let cC: class C
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt11.a: |- ( ph -> ( x e. X |-> A ) e. ( J Cn K ) )
  assume cnmpt1t.b: |- ( ph -> ( x e. X |-> B ) e. ( J Cn L ) )

  disjoint ph x
  disjoint J x
  disjoint X x
  disjoint K x
  disjoint L x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J y
  disjoint x z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint K y
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint B y
  disjoint C x
  assert |- ( ph -> ( x e. X |-> <. A , B >. ) e. ( J Cn ( K tX L ) ) )

  proof
    wph
    vx
    cJ
    cuni
    #
    vx
    cv
    #
    vx
    cX
    cA
    cmpt
    #
    cfv
    #
    @1
    vx
    cX
    cB
    cmpt
    #
    cfv
    #
    cop
    #
    cmpt
    #
    vx
    cX
    cA
    cB
    cop
    #
    cmpt
    #
    cJ
    cK
    cL
    ctx
    co
    ccn
    co
    #
    wph
    vx
    cX
    @6
    cmpt
    #
    @7
    @9
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cX
    @0
    wceq
    @11
    @7
    wceq
    cnmptid.j
    cX
    cJ
    toponuni
    vx
    cX
    @0
    @6
    mpteq1
    3syl
    wph
    vx
    cX
    @6
    @8
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @3
    cA
    @5
    cB
    @14
    @13
    cA
    cK
    cuni
    #
    wcel
    #
    @3
    cA
    wceq
    wph
    @13
    simpr
    #
    wph
    @16
    vx
    cX
    wph
    cX
    @15
    @2
    wf
    #
    @16
    vx
    cX
    wral
    wph
    @12
    cK
    @15
    ctopon
    cfv
    wcel
    #
    @2
    cJ
    cK
    ccn
    co
    wcel
    #
    @18
    cnmptid.j
    wph
    cK
    ctop
    wcel
    #
    @19
    wph
    @20
    @21
    cnmpt11.a
    @2
    cJ
    cK
    cntop2
    syl
    cK
    @15
    @15
    eqid
    toptopon
    sylib
    cnmpt11.a
    @2
    cJ
    cK
    cX
    @15
    cnf2
    syl3anc
    vx
    cX
    @15
    cA
    @2
    @2
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    vx
    cX
    cA
    @15
    @2
    @22
    fvmpt2
    syl2anc
    @14
    @13
    cB
    cL
    cuni
    #
    wcel
    #
    @5
    cB
    wceq
    @17
    wph
    @24
    vx
    cX
    wph
    cX
    @23
    @4
    wf
    #
    @24
    vx
    cX
    wral
    wph
    @12
    cL
    @23
    ctopon
    cfv
    wcel
    #
    @4
    cJ
    cL
    ccn
    co
    wcel
    #
    @25
    cnmptid.j
    wph
    cL
    ctop
    wcel
    #
    @26
    wph
    @27
    @28
    cnmpt1t.b
    @4
    cJ
    cL
    cntop2
    syl
    cL
    @23
    @23
    eqid
    toptopon
    sylib
    cnmpt1t.b
    @4
    cJ
    cL
    cX
    @23
    cnf2
    syl3anc
    vx
    cX
    @23
    cB
    @4
    @4
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    vx
    cX
    cB
    @23
    @4
    @29
    fvmpt2
    syl2anc
    opeq12d
    mpteq2dva
    eqtr3d
    wph
    @20
    @27
    @7
    @10
    wcel
    cnmpt11.a
    cnmpt1t.b
    vy
    cK
    cL
    cJ
    @2
    @4
    @7
    @0
    @0
    eqid
    vx
    vy
    @0
    @6
    vy
    cv
    #
    @2
    cfv
    #
    @30
    @4
    cfv
    #
    cop
    vy
    @6
    nfcv
    vx
    @31
    @32
    vx
    cX
    cA
    @30
    nffvmpt1
    vx
    cX
    cB
    @30
    nffvmpt1
    nfop
    @1
    @30
    wceq
    @3
    @31
    @5
    @32
    @1
    @30
    @2
    fveq2
    @1
    @30
    @4
    fveq2
    opeq12d
    cbvmpt
    txcnmpt
    syl2anc
    eqeltrrd
end
