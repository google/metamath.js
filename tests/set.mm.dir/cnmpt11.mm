include "cmpt.mm"
include "ccom.mm"
include "ccn.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wf.mm"
include "ctopon.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cuni.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "adantr.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "eqtrd.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfco.mm"
include "nffv.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "wfn.mm"
include "wb.mm"
include "fco.mm"
include "ffn.mm"
include "fmptd.mm"
include "eqfnfv.mm"
include "mpbird.mm"
include "cnco.mm"
include "eqeltrrd.mm"

theorem cnmpt11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vz: setvar z
  let cD: class D
  let cF: class F
  let cM: class M
  let cZ: class Z
  let cP: class P
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt11.a: |- ( ph -> ( x e. X |-> A ) e. ( J Cn K ) )
  assume cnmpt11.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt11.b: |- ( ph -> ( y e. Y |-> B ) e. ( K Cn L ) )
  assume cnmpt11.c: |- ( y = A -> B = C )

  disjoint B x
  disjoint C y
  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint y z
  disjoint C z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint X z
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( x e. X |-> C ) e. ( J Cn L ) )

  proof
    wph
    vy
    cY
    cB
    cmpt
    #
    vx
    cX
    cA
    cmpt
    #
    ccom
    #
    vx
    cX
    cC
    cmpt
    #
    cJ
    cL
    ccn
    co
    #
    wph
    @2
    @3
    wceq
    #
    vz
    cv
    #
    @2
    cfv
    #
    @6
    @3
    cfv
    #
    wceq
    #
    vz
    cX
    wral
    #
    wph
    vx
    cv
    #
    @2
    cfv
    #
    @11
    @3
    cfv
    #
    wceq
    #
    vx
    cX
    wral
    @10
    wph
    @14
    vx
    cX
    wph
    @11
    cX
    wcel
    #
    wa
    #
    @11
    @1
    cfv
    #
    @0
    cfv
    #
    cC
    @12
    @13
    @16
    @18
    cA
    @0
    cfv
    #
    cC
    @16
    @17
    cA
    @0
    @16
    @15
    cA
    cY
    wcel
    #
    @17
    cA
    wceq
    wph
    @15
    simpr
    #
    wph
    @20
    vx
    cX
    wph
    cX
    cY
    @1
    wf
    #
    @20
    vx
    cX
    wral
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
    #
    @1
    cJ
    cK
    ccn
    co
    wcel
    #
    @22
    cnmptid.j
    cnmpt11.k
    cnmpt11.a
    @1
    cJ
    cK
    cX
    cY
    cnf2
    syl3anc
    #
    vx
    cX
    cY
    cA
    @1
    @1
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    #
    vx
    cX
    cA
    cY
    @1
    @26
    fvmpt2
    syl2anc
    fveq2d
    @16
    @20
    cC
    cL
    cuni
    #
    wcel
    #
    @19
    cC
    wceq
    @27
    @16
    @20
    cB
    @28
    wcel
    #
    vy
    cY
    wral
    #
    @29
    @27
    wph
    @31
    @15
    wph
    cY
    @28
    @0
    wf
    #
    @31
    wph
    @23
    cL
    @28
    ctopon
    cfv
    wcel
    #
    @0
    cK
    cL
    ccn
    co
    wcel
    #
    @32
    cnmpt11.k
    wph
    cL
    ctop
    wcel
    #
    @33
    wph
    @34
    @35
    cnmpt11.b
    @0
    cK
    cL
    cntop2
    syl
    cL
    @28
    @28
    eqid
    toptopon
    sylib
    cnmpt11.b
    @0
    cK
    cL
    cY
    @28
    cnf2
    syl3anc
    #
    vy
    cY
    @28
    cB
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    adantr
    @30
    @29
    vy
    cA
    cY
    vy
    cv
    cA
    wceq
    cB
    cC
    @28
    cnmpt11.c
    eleq1d
    rspcv
    sylc
    #
    vy
    cA
    cB
    cC
    cY
    @28
    @0
    cnmpt11.c
    @37
    fvmptg
    syl2anc
    eqtrd
    wph
    @22
    @15
    @12
    @18
    wceq
    @25
    cX
    cY
    @11
    @0
    @1
    fvco3
    sylan
    @16
    @15
    @29
    @13
    cC
    wceq
    @21
    @38
    vx
    cX
    cC
    @28
    @3
    @3
    eqid
    #
    fvmpt2
    syl2anc
    3eqtr4d
    ralrimiva
    @14
    @9
    vx
    vz
    cX
    @14
    vz
    nfv
    vx
    @7
    @8
    vx
    @6
    @2
    vx
    @0
    @1
    vx
    @0
    nfcv
    vx
    cX
    cA
    nfmpt1
    nfco
    vx
    @6
    nfcv
    #
    nffv
    vx
    @6
    @3
    vx
    cX
    cC
    nfmpt1
    @40
    nffv
    nfeq
    @11
    @6
    wceq
    @12
    @7
    @13
    @8
    @11
    @6
    @2
    fveq2
    @11
    @6
    @3
    fveq2
    eqeq12d
    cbvral
    sylib
    wph
    @2
    cX
    wfn
    #
    @3
    cX
    wfn
    #
    @5
    @10
    wb
    wph
    cX
    @28
    @2
    wf
    #
    @41
    wph
    @32
    @22
    @43
    @36
    @25
    cX
    cY
    @28
    @0
    @1
    fco
    syl2anc
    cX
    @28
    @2
    ffn
    syl
    wph
    cX
    @28
    @3
    wf
    @42
    wph
    vx
    cX
    cC
    @28
    @3
    @38
    @39
    fmptd
    cX
    @28
    @3
    ffn
    syl
    vz
    cX
    @2
    @3
    eqfnfv
    syl2anc
    mpbird
    wph
    @24
    @34
    @2
    @4
    wcel
    cnmpt11.a
    cnmpt11.b
    @1
    @0
    cJ
    cK
    cL
    cnco
    syl2anc
    eqeltrrd
end
