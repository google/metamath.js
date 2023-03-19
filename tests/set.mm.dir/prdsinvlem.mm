include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cminusg.mm"
include "cmpt.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "cgrp.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "prdsbasmpt.mm"
include "mpbird.mm"
include "syl5eqel.mm"
include "cplusg.mm"
include "c0g.mm"
include "grplinv.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "oveq1d.mm"
include "ccom.mm"
include "fveq1i.mm"
include "fvco2.mm"
include "sylan.mm"
include "syl5eq.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "prdsplusgval.mm"
include "cvv.mm"
include "crn.mm"
include "wss.mm"
include "fn0g.mm"
include "a1i.mm"
include "ssv.mm"
include "fnco.mm"
include "syl3anc.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "dffn5.mm"
include "sylib.mm"
include "jca.mm"

theorem prdsinvlem
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  assume prdsinvlem.y: |- Y = ( S Xs_ R )
  assume prdsinvlem.b: |- B = ( Base ` Y )
  assume prdsinvlem.p: |- .+ = ( +g ` Y )
  assume prdsinvlem.s: |- ( ph -> S e. V )
  assume prdsinvlem.i: |- ( ph -> I e. W )
  assume prdsinvlem.r: |- ( ph -> R : I --> Grp )
  assume prdsinvlem.f: |- ( ph -> F e. B )
  assume prdsinvlem.z: |- .0. = ( 0g o. R )
  assume prdsinvlem.n: |- N = ( y e. I |-> ( ( invg ` ( R ` y ) ) ` ( F ` y ) ) )

  disjoint B y
  disjoint F y
  disjoint I y
  disjoint ph y
  disjoint R y
  disjoint S y
  disjoint V y
  disjoint W y
  disjoint Y y
  disjoint x y
  disjoint B x
  disjoint F x
  disjoint I x
  disjoint N x
  disjoint ph x
  disjoint R x
  disjoint .+ x
  disjoint S x
  disjoint V x
  disjoint W x
  disjoint Y x
  disjoint .0. x
  assert |- ( ph -> ( N e. B /\ ( N .+ F ) = .0. ) )

  proof
    wph
    cN
    cB
    wcel
    cN
    cF
    c.pl
    co
    #
    c.0
    wceq
    wph
    cN
    vy
    cI
    vy
    cv
    #
    cF
    cfv
    #
    @1
    cR
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    cmpt
    #
    cB
    prdsinvlem.n
    wph
    @6
    cB
    wcel
    @5
    @3
    cbs
    cfv
    #
    wcel
    #
    vy
    cI
    wral
    wph
    @8
    vy
    cI
    wph
    @1
    cI
    wcel
    #
    wa
    #
    @3
    cgrp
    wcel
    @2
    @7
    wcel
    @8
    wph
    cI
    cgrp
    @1
    cR
    prdsinvlem.r
    ffvelrnda
    @10
    cB
    cR
    cS
    cF
    cI
    @1
    cV
    cW
    cY
    prdsinvlem.y
    prdsinvlem.b
    wph
    cS
    cV
    wcel
    #
    @9
    prdsinvlem.s
    adantr
    wph
    cI
    cW
    wcel
    #
    @9
    prdsinvlem.i
    adantr
    wph
    cR
    cI
    wfn
    #
    @9
    wph
    cI
    cgrp
    cR
    wf
    @13
    prdsinvlem.r
    cI
    cgrp
    cR
    ffn
    syl
    #
    adantr
    wph
    cF
    cB
    wcel
    #
    @9
    prdsinvlem.f
    adantr
    wph
    @9
    simpr
    prdsbasprj
    @7
    @3
    @4
    @2
    @7
    eqid
    @4
    eqid
    grpinvcl
    syl2anc
    ralrimiva
    wph
    vy
    cB
    cR
    cS
    @5
    cI
    cV
    cW
    cY
    prdsinvlem.y
    prdsinvlem.b
    prdsinvlem.s
    prdsinvlem.i
    @14
    prdsbasmpt
    mpbird
    syl5eqel
    #
    wph
    vx
    cI
    vx
    cv
    #
    cN
    cfv
    #
    @17
    cF
    cfv
    #
    @17
    cR
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    vx
    cI
    @17
    c.0
    cfv
    #
    cmpt
    #
    @0
    c.0
    wph
    vx
    cI
    @22
    @23
    wph
    @17
    cI
    wcel
    #
    wa
    #
    @19
    @20
    cminusg
    cfv
    #
    cfv
    #
    @19
    @21
    co
    #
    @20
    c0g
    cfv
    #
    @22
    @23
    @26
    @20
    cgrp
    wcel
    @19
    @20
    cbs
    cfv
    #
    wcel
    @29
    @30
    wceq
    wph
    cI
    cgrp
    @17
    cR
    prdsinvlem.r
    ffvelrnda
    @26
    cB
    cR
    cS
    cF
    cI
    @17
    cV
    cW
    cY
    prdsinvlem.y
    prdsinvlem.b
    wph
    @11
    @25
    prdsinvlem.s
    adantr
    wph
    @12
    @25
    prdsinvlem.i
    adantr
    wph
    @13
    @25
    @14
    adantr
    wph
    @15
    @25
    prdsinvlem.f
    adantr
    wph
    @25
    simpr
    prdsbasprj
    @31
    @21
    @20
    @27
    @19
    @30
    @31
    eqid
    @21
    eqid
    @30
    eqid
    @27
    eqid
    grplinv
    syl2anc
    @26
    @18
    @28
    @19
    @21
    @25
    @18
    @28
    wceq
    wph
    vy
    @17
    @5
    @28
    cI
    cN
    vy
    vx
    weq
    #
    @2
    @19
    @4
    @27
    @32
    @3
    @20
    cminusg
    @1
    @17
    cR
    fveq2
    fveq2d
    @1
    @17
    cF
    fveq2
    fveq12d
    prdsinvlem.n
    @19
    @27
    fvex
    fvmpt
    adantl
    oveq1d
    @26
    @23
    @17
    c0g
    cR
    ccom
    #
    cfv
    #
    @30
    @17
    c.0
    @33
    prdsinvlem.z
    fveq1i
    wph
    @13
    @25
    @34
    @30
    wceq
    @14
    cI
    c0g
    cR
    @17
    fvco2
    sylan
    syl5eq
    3eqtr4d
    mpteq2dva
    wph
    vx
    cB
    c.pl
    cR
    cS
    cN
    cF
    cI
    cV
    cW
    cY
    prdsinvlem.y
    prdsinvlem.b
    prdsinvlem.s
    prdsinvlem.i
    @14
    @16
    prdsinvlem.f
    prdsinvlem.p
    prdsplusgval
    wph
    c.0
    cI
    wfn
    #
    c.0
    @24
    wceq
    wph
    @33
    cI
    wfn
    #
    @35
    wph
    c0g
    cvv
    wfn
    #
    @13
    cR
    crn
    #
    cvv
    wss
    #
    @36
    @37
    wph
    fn0g
    a1i
    @14
    @39
    wph
    @38
    ssv
    a1i
    cvv
    cI
    c0g
    cR
    fnco
    syl3anc
    cI
    c.0
    @33
    prdsinvlem.z
    fneq1i
    sylibr
    vx
    cI
    c.0
    dffn5
    sylib
    3eqtr4d
    jca
end
