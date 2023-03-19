include "cof.mm"
include "cseq.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "wfn.mm"
include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cvv.mm"
include "wral.mm"
include "fvex.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "fneq1.mm"
include "elab.mm"
include "sylibr.mm"
include "simprl.mm"
include "simprr.mm"
include "adantr.mm"
include "inidm.mm"
include "offn.mm"
include "ex.mm"
include "vex.mm"
include "anbi12i.mm"
include "ovex.mm"
include "3imtr4g.mm"
include "imp.mm"
include "seqcl.mm"
include "sylib.mm"
include "dffn5.mm"
include "fveq1.mm"
include "fvmpt.mm"
include "adantlr.mm"
include "cuz.mm"
include "eqidd.mm"
include "ofval.mm"
include "an32s.mm"
include "ax-mp.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "sylan2b.mm"
include "fveq1d.mm"
include "simplr.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "seqhomo.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"

theorem seqof
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let vy: setvar y
  let vw: setvar w
  assume seqof.1: |- ( ph -> A e. V )
  assume seqof.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqof.3: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) = ( z e. A |-> ( G ` x ) ) )

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint F x
  disjoint F z
  disjoint G x
  disjoint M x
  disjoint M z
  disjoint N x
  disjoint N z
  disjoint .+ x
  disjoint .+ z
  disjoint ph x
  disjoint ph z
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F y
  disjoint M w
  disjoint M y
  disjoint N w
  disjoint N y
  disjoint .+ w
  disjoint .+ y
  disjoint ph y
  assert |- ( ph -> ( seq M ( oF .+ , F ) ` N ) = ( z e. A |-> ( seq M ( .+ , G ) ` N ) ) )

  proof
    wph
    cN
    c.pl
    cof
    #
    cF
    cM
    cseq
    #
    cfv
    #
    vz
    cA
    vz
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    vz
    cA
    cN
    c.pl
    cG
    cM
    cseq
    cfv
    #
    cmpt
    wph
    @2
    cA
    wfn
    #
    @2
    @5
    wceq
    wph
    @2
    @3
    cA
    wfn
    #
    vz
    cab
    #
    wcel
    @7
    wph
    vx
    vy
    @0
    @9
    cF
    cM
    cN
    seqof.2
    wph
    vx
    cv
    #
    cM
    cN
    cfz
    co
    wcel
    #
    wa
    #
    @10
    cF
    cfv
    #
    cA
    wfn
    #
    @13
    @9
    wcel
    #
    @12
    @14
    vz
    cA
    @10
    cG
    cfv
    #
    cmpt
    #
    cA
    wfn
    #
    @16
    cvv
    wcel
    #
    vz
    cA
    wral
    @18
    @12
    @19
    vz
    cA
    @10
    cG
    fvex
    #
    rgenw
    vz
    cA
    @16
    @17
    cvv
    @17
    eqid
    #
    fnmpt
    mp1i
    @12
    cA
    @13
    @17
    seqof.3
    fneq1d
    mpbird
    @8
    @14
    vz
    @13
    @10
    cF
    fvex
    #
    cA
    @3
    @13
    fneq1
    elab
    sylibr
    #
    wph
    @10
    @9
    wcel
    #
    vy
    cv
    #
    @9
    wcel
    #
    wa
    #
    @10
    @25
    @0
    co
    #
    @9
    wcel
    #
    wph
    @10
    cA
    wfn
    #
    @25
    cA
    wfn
    #
    wa
    #
    @28
    cA
    wfn
    #
    @27
    @29
    wph
    @32
    @33
    wph
    @32
    wa
    #
    cA
    cA
    c.pl
    cA
    @10
    @25
    cV
    cV
    wph
    @30
    @31
    simprl
    #
    wph
    @30
    @31
    simprr
    #
    wph
    cA
    cV
    wcel
    @32
    seqof.1
    adantr
    #
    @37
    cA
    inidm
    #
    offn
    ex
    @24
    @30
    @26
    @31
    @8
    @30
    vz
    @10
    vx
    vex
    #
    cA
    @3
    @10
    fneq1
    elab
    @8
    @31
    vz
    @25
    vy
    vex
    #
    cA
    @3
    @25
    fneq1
    elab
    anbi12i
    #
    @8
    @33
    vz
    @28
    @10
    @25
    @0
    ovex
    #
    cA
    @3
    @28
    fneq1
    elab
    3imtr4g
    imp
    #
    seqcl
    @8
    @7
    vz
    @2
    cN
    @1
    fvex
    #
    cA
    @3
    @2
    fneq1
    elab
    sylib
    vz
    cA
    @2
    dffn5
    sylib
    wph
    vz
    cA
    @4
    @6
    wph
    @3
    cA
    wcel
    #
    wa
    #
    @2
    vw
    cvv
    @3
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    @4
    @6
    @2
    cvv
    wcel
    @50
    @4
    wceq
    @46
    @44
    vw
    @2
    @48
    @4
    cvv
    @49
    @3
    @47
    @2
    fveq1
    @49
    eqid
    #
    @3
    @2
    fvex
    fvmpt
    mp1i
    @46
    vx
    vy
    @0
    c.pl
    @9
    cF
    cG
    @49
    cM
    cN
    wph
    @27
    @29
    @45
    @43
    adantlr
    wph
    @11
    @15
    @45
    @23
    adantlr
    wph
    cN
    cM
    cuz
    cfv
    wcel
    @45
    seqof.2
    adantr
    @27
    @46
    @32
    @28
    @49
    cfv
    #
    @10
    @49
    cfv
    #
    @25
    @49
    cfv
    #
    c.pl
    co
    #
    wceq
    @41
    @46
    @32
    wa
    @3
    @28
    cfv
    #
    @3
    @10
    cfv
    #
    @3
    @25
    cfv
    #
    c.pl
    co
    #
    @52
    @55
    wph
    @32
    @45
    @56
    @59
    wceq
    @34
    cA
    cA
    @57
    @58
    c.pl
    cA
    @10
    @25
    cV
    cV
    @3
    @35
    @36
    @37
    @37
    @38
    @34
    @45
    wa
    #
    @57
    eqidd
    @60
    @58
    eqidd
    ofval
    an32s
    @28
    cvv
    wcel
    @52
    @56
    wceq
    @42
    vw
    @28
    @48
    @56
    cvv
    @49
    @3
    @47
    @28
    fveq1
    @51
    @3
    @28
    fvex
    fvmpt
    ax-mp
    @53
    @57
    @54
    @58
    c.pl
    @10
    cvv
    wcel
    @53
    @57
    wceq
    @39
    vw
    @10
    @48
    @57
    cvv
    @49
    @3
    @47
    @10
    fveq1
    @51
    @3
    @10
    fvex
    fvmpt
    ax-mp
    @25
    cvv
    wcel
    @54
    @58
    wceq
    @40
    vw
    @25
    @48
    @58
    cvv
    @49
    @3
    @47
    @25
    fveq1
    @51
    @3
    @25
    fvex
    fvmpt
    ax-mp
    oveq12i
    3eqtr4g
    sylan2b
    @46
    @11
    wa
    #
    @13
    @49
    cfv
    #
    @3
    @13
    cfv
    #
    @16
    @13
    cvv
    wcel
    @62
    @63
    wceq
    @22
    vw
    @13
    @48
    @63
    cvv
    @49
    @3
    @47
    @13
    fveq1
    @51
    @3
    @13
    fvex
    fvmpt
    ax-mp
    @61
    @63
    @3
    @17
    cfv
    #
    @16
    @61
    @3
    @13
    @17
    wph
    @11
    @13
    @17
    wceq
    @45
    seqof.3
    adantlr
    fveq1d
    @61
    @45
    @19
    @64
    @16
    wceq
    wph
    @45
    @11
    simplr
    @20
    vz
    cA
    @16
    cvv
    @17
    @21
    fvmpt2
    sylancl
    eqtrd
    syl5eq
    seqhomo
    eqtr3d
    mpteq2dva
    eqtrd
end
