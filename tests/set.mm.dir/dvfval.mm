include "cc.mm"
include "wss.mm"
include "wf.mm"
include "w3a.mm"
include "cdv.mm"
include "co.mm"
include "cnt.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cxp.mm"
include "ciun.mm"
include "wceq.mm"
include "cpw.mm"
include "cpm.mm"
include "cdm.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cvv.mm"
include "cmpt2.mm"
include "df-dv.mm"
include "a1i.mm"
include "wa.mm"
include "oveq1i.mm"
include "simprl.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "simprr.mm"
include "dmeqd.mm"
include "simpl2.mm"
include "fdm.mm"
include "syl.mm"
include "eqtrd.mm"
include "fveq12d.mm"
include "difeq1d.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "xpeq2d.mm"
include "iuneq12d.mm"
include "simpr.mm"
include "wcel.mm"
include "simp1.mm"
include "cnex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "simp2.mm"
include "simp3.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "wral.mm"
include "limccl.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "rgenw.mm"
include "ss2iun.mm"
include "iunxpconst.mm"
include "sseqtri.mm"
include "fvex.mm"
include "xpex.mm"
include "ssex.mm"
include "ovmpt2dx.mm"
include "eqsstrd.mm"
include "jca.mm"

theorem dvfval
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let vf: setvar f
  let vs: setvar s
  let cB: class B
  let cC: class C
  let cG: class G
  assume dvval.t: |- T = ( K |`t S )
  assume dvval.k: |- K = ( TopOpen ` CCfld )

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint F x
  disjoint F z
  disjoint K x
  disjoint K z
  disjoint S x
  disjoint S z
  disjoint T x
  disjoint f s
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint s x
  disjoint s z
  disjoint A s
  disjoint B x
  disjoint B z
  disjoint F f
  disjoint F s
  disjoint C x
  disjoint C z
  disjoint K f
  disjoint K s
  disjoint S f
  disjoint S s
  disjoint T f
  disjoint T s
  disjoint G x
  assert |- ( ( S C_ CC /\ F : A --> CC /\ A C_ S ) -> ( ( S _D F ) = U_ x e. ( ( int ` T ) ` A ) ( { x } X. ( ( z e. ( A \ { x } ) |-> ( ( ( F ` z ) - ( F ` x ) ) / ( z - x ) ) ) limCC x ) ) /\ ( S _D F ) C_ ( ( ( int ` T ) ` A ) X. CC ) ) )

  proof
    cS
    cc
    wss
    #
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    #
    w3a
    #
    cS
    cF
    cdv
    co
    #
    vx
    cA
    cT
    cnt
    cfv
    #
    cfv
    #
    vx
    cv
    #
    csn
    #
    vz
    cA
    @8
    cdif
    #
    vz
    cv
    #
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cmin
    co
    #
    @10
    @7
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @7
    climc
    co
    #
    cxp
    #
    ciun
    #
    wceq
    @4
    @6
    cc
    cxp
    #
    wss
    @3
    vs
    vf
    cS
    cF
    cc
    cpw
    #
    cc
    vs
    cv
    #
    cpm
    co
    #
    vx
    vf
    cv
    #
    cdm
    #
    ccnfld
    ctopn
    cfv
    #
    @22
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @8
    vz
    @25
    @8
    cdif
    #
    @10
    @24
    cfv
    #
    @7
    @24
    cfv
    #
    cmin
    co
    #
    @14
    cdiv
    co
    #
    cmpt
    #
    @7
    climc
    co
    #
    cxp
    #
    ciun
    #
    @19
    cdv
    cc
    cS
    cpm
    co
    #
    cvv
    cdv
    vs
    vf
    @21
    @23
    @38
    cmpt2
    wceq
    @3
    vx
    vz
    vf
    vs
    df-dv
    a1i
    @3
    @22
    cS
    wceq
    #
    @24
    cF
    wceq
    #
    wa
    #
    wa
    #
    vx
    @29
    @6
    @37
    @18
    @43
    @25
    cA
    @28
    @5
    @43
    @27
    cT
    cnt
    @43
    @27
    cK
    @22
    crest
    co
    #
    cT
    cK
    @26
    @22
    crest
    dvval.k
    oveq1i
    @43
    @44
    cK
    cS
    crest
    co
    cT
    @43
    @22
    cS
    cK
    crest
    @3
    @40
    @41
    simprl
    oveq2d
    dvval.t
    syl6eqr
    syl5eqr
    fveq2d
    @43
    @25
    cF
    cdm
    #
    cA
    @43
    @24
    cF
    @3
    @40
    @41
    simprr
    #
    dmeqd
    @43
    @1
    @45
    cA
    wceq
    @0
    @1
    @2
    @42
    simpl2
    cA
    cc
    cF
    fdm
    syl
    eqtrd
    #
    fveq12d
    @43
    @36
    @17
    @8
    @43
    @35
    @16
    @7
    climc
    @43
    vz
    @30
    @34
    @9
    @15
    @43
    @25
    cA
    @8
    @47
    difeq1d
    @43
    @33
    @13
    @14
    cdiv
    @43
    @31
    @11
    @32
    @12
    cmin
    @43
    @10
    @24
    cF
    @46
    fveq1d
    @43
    @7
    @24
    cF
    @46
    fveq1d
    oveq12d
    oveq1d
    mpteq12dv
    oveq1d
    xpeq2d
    iuneq12d
    @3
    @40
    wa
    @22
    cS
    cc
    cpm
    @3
    @40
    simpr
    oveq2d
    @3
    @0
    cS
    @21
    wcel
    #
    @0
    @1
    @2
    simp1
    cS
    cc
    cnex
    elpw2
    sylibr
    #
    @3
    cc
    cvv
    wcel
    #
    @48
    @1
    @2
    cF
    @39
    wcel
    @50
    @3
    cnex
    a1i
    @49
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    cc
    cS
    cA
    cF
    cvv
    @21
    elpm2r
    syl22anc
    @3
    @19
    @20
    wss
    #
    @19
    cvv
    wcel
    @51
    @3
    @19
    vx
    @6
    @8
    cc
    cxp
    #
    ciun
    #
    @20
    @18
    @52
    wss
    #
    vx
    @6
    wral
    @19
    @53
    wss
    @54
    vx
    @6
    @17
    cc
    wss
    @54
    @7
    @16
    limccl
    @17
    cc
    @8
    xpss2
    ax-mp
    rgenw
    vx
    @6
    @18
    @52
    ss2iun
    ax-mp
    vx
    @6
    cc
    iunxpconst
    sseqtri
    a1i
    #
    @19
    @20
    @6
    cc
    cA
    @5
    fvex
    cnex
    xpex
    ssex
    syl
    ovmpt2dx
    #
    @3
    @4
    @19
    @20
    @56
    @55
    eqsstrd
    jca
end
