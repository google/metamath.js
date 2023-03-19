include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "cc.mm"
include "wss.mm"
include "wf.mm"
include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "cxp.mm"
include "csn.mm"
include "ccnfld.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "ctsu.mm"
include "ciun.mm"
include "taylfval.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "snssd.mm"
include "taylfvallem.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "wi.mm"
include "eltayl.mm"
include "biimpd.mm"
include "alrimiv.mm"
include "ctopn.mm"
include "cvv.mm"
include "cnfldbas.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "ctps.mm"
include "cnfldtps.mm"
include "a1i.mm"
include "ovex.mm"
include "inex1.mm"
include "taylfvallem1.mm"
include "eqid.mm"
include "fmptd.mm"
include "cha.mm"
include "cnfldhaus.mm"
include "haustsms.mm"
include "ex.mm"
include "moanimv.mm"
include "moim.mm"
include "sylc.mm"
include "dffun6.mm"
include "sylanbrc.mm"
include "funfn.mm"
include "sylib.mm"
include "rnss.mm"
include "syl.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "df-f.mm"

theorem taylf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
  let cX: class X
  assume taylfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylfval.f: |- ( ph -> F : A --> CC )
  assume taylfval.a: |- ( ph -> A C_ S )
  assume taylfval.n: |- ( ph -> ( N e. NN0 \/ N = +oo ) )
  assume taylfval.b: |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )
  assume taylfval.t: |- T = ( N ( S Tayl F ) B )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint N k
  disjoint S k
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a f
  disjoint a s
  disjoint F a
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint k s
  disjoint n s
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint f ph
  disjoint n ph
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint Y x
  disjoint N a
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S n
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint X k
  disjoint X x
  assert |- ( ph -> T : dom T --> CC )

  proof
    wph
    cT
    cT
    cdm
    #
    wfn
    #
    cT
    crn
    #
    cc
    wss
    @0
    cc
    cT
    wf
    wph
    cT
    wfun
    #
    @1
    wph
    cT
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    @3
    wph
    cT
    cc
    cc
    cxp
    #
    wss
    #
    @9
    wrel
    @4
    wph
    cT
    vx
    cc
    @5
    csn
    #
    ccnfld
    vk
    cc0
    cN
    cicc
    co
    #
    cz
    cin
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    cfv
    cfv
    @14
    cfa
    cfv
    cdiv
    co
    @5
    cB
    cmin
    co
    @14
    cexp
    co
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    cxp
    #
    ciun
    #
    @9
    wph
    vx
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfval.t
    taylfval
    wph
    @18
    @9
    wss
    #
    vx
    cc
    wral
    @19
    @9
    wss
    wph
    @20
    vx
    cc
    wph
    @5
    cc
    wcel
    #
    wa
    #
    @11
    cc
    wss
    @17
    cc
    wss
    @20
    @22
    @5
    cc
    wph
    @21
    simpr
    snssd
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    @5
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfvallem
    @11
    cc
    @17
    cc
    xpss12
    syl2anc
    ralrimiva
    vx
    cc
    @18
    @9
    iunss
    sylibr
    eqsstrd
    #
    cc
    cc
    relxp
    cT
    @9
    relss
    mpisyl
    wph
    @8
    vx
    wph
    @7
    @21
    @6
    @17
    wcel
    #
    wa
    #
    wi
    #
    vy
    wal
    @25
    vy
    wmo
    #
    @8
    wph
    @26
    vy
    wph
    @7
    @25
    wph
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    @5
    @6
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfval.t
    eltayl
    biimpd
    alrimiv
    wph
    @21
    @24
    vy
    wmo
    #
    wi
    @27
    wph
    @21
    @28
    @22
    vy
    @13
    cc
    @16
    ccnfld
    ccnfld
    ctopn
    cfv
    #
    cvv
    cnfldbas
    ccnfld
    crg
    wcel
    ccnfld
    ccmn
    wcel
    @22
    cnring
    ccnfld
    ringcmn
    mp1i
    ccnfld
    ctps
    wcel
    @22
    cnfldtps
    a1i
    @13
    cvv
    wcel
    @22
    @12
    cz
    cc0
    cN
    cicc
    ovex
    inex1
    a1i
    @22
    vk
    @13
    @15
    cc
    @16
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    @5
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfvallem1
    @16
    eqid
    fmptd
    @29
    eqid
    #
    @29
    cha
    wcel
    @22
    @29
    @30
    cnfldhaus
    a1i
    haustsms
    ex
    @21
    @24
    vy
    moanimv
    sylibr
    @7
    @25
    vy
    moim
    sylc
    alrimiv
    vx
    vy
    cT
    dffun6
    sylanbrc
    cT
    funfn
    sylib
    wph
    @2
    @9
    crn
    #
    cc
    wph
    @10
    @2
    @31
    wss
    @23
    cT
    @9
    rnss
    syl
    cc
    cc
    rnxpss
    syl6ss
    @0
    cc
    cT
    df-f
    sylanbrc
end
