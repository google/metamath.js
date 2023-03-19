include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cfv.mm"
include "c0g.mm"
include "cmpt.mm"
include "ccom.mm"
include "cvv.mm"
include "fvexd.mm"
include "cmnd.mm"
include "feqmptd.mm"
include "wfn.mm"
include "fn0g.mm"
include "a1i.mm"
include "dffn5.mm"
include "sylib.mm"
include "fveq2.mm"
include "fmptco.mm"
include "syl5eq.mm"
include "cbs.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "mndidcl.mm"
include "syl.mm"
include "ralrimiva.mm"
include "wf.mm"
include "ffn.mm"
include "prdsbasmpt.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "cplusg.mm"
include "fveq1i.mm"
include "fvco2.mm"
include "sylan.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "prdsplusgval.mm"
include "prdsbasfn.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "mndrid.mm"
include "jca.mm"

theorem prdsidlem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vy: setvar y
  let cF: class F
  let cG: class G
  assume prdsplusgcl.y: |- Y = ( S Xs_ R )
  assume prdsplusgcl.b: |- B = ( Base ` Y )
  assume prdsplusgcl.p: |- .+ = ( +g ` Y )
  assume prdsplusgcl.s: |- ( ph -> S e. V )
  assume prdsplusgcl.i: |- ( ph -> I e. W )
  assume prdsplusgcl.r: |- ( ph -> R : I --> Mnd )
  assume prdsidlem.z: |- .0. = ( 0g o. R )

  disjoint .+ x
  disjoint B x
  disjoint I x
  disjoint R x
  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint W x
  disjoint Y x
  disjoint x y
  disjoint .+ y
  disjoint .0. y
  disjoint B y
  disjoint F x
  disjoint I y
  disjoint R y
  disjoint G x
  disjoint ph y
  disjoint S y
  disjoint V y
  disjoint W y
  disjoint Y y
  assert |- ( ph -> ( .0. e. B /\ A. x e. B ( ( .0. .+ x ) = x /\ ( x .+ .0. ) = x ) ) )

  proof
    wph
    c.0
    cB
    wcel
    #
    c.0
    vx
    cv
    #
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    c.0
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cB
    wral
    wph
    c.0
    vy
    cI
    vy
    cv
    #
    cR
    cfv
    #
    c0g
    cfv
    #
    cmpt
    #
    cB
    wph
    c.0
    c0g
    cR
    ccom
    #
    @10
    prdsidlem.z
    wph
    vy
    vx
    cI
    cvv
    @8
    @1
    c0g
    cfv
    #
    @9
    cR
    c0g
    wph
    @7
    cI
    wcel
    #
    wa
    #
    @7
    cR
    fvexd
    wph
    vy
    cI
    cmnd
    cR
    prdsplusgcl.r
    feqmptd
    wph
    c0g
    cvv
    wfn
    #
    c0g
    vx
    cvv
    @12
    cmpt
    wceq
    @15
    wph
    fn0g
    a1i
    vx
    cvv
    c0g
    dffn5
    sylib
    @1
    @8
    c0g
    fveq2
    fmptco
    syl5eq
    wph
    @10
    cB
    wcel
    @9
    @8
    cbs
    cfv
    #
    wcel
    #
    vy
    cI
    wral
    wph
    @17
    vy
    cI
    @14
    @8
    cmnd
    wcel
    #
    @17
    wph
    cI
    cmnd
    @7
    cR
    prdsplusgcl.r
    ffvelrnda
    @16
    @8
    @9
    @16
    eqid
    #
    @9
    eqid
    #
    mndidcl
    syl
    ralrimiva
    wph
    vy
    cB
    cR
    cS
    @9
    cI
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    prdsplusgcl.s
    prdsplusgcl.i
    wph
    cI
    cmnd
    cR
    wf
    #
    cR
    cI
    wfn
    #
    prdsplusgcl.r
    cI
    cmnd
    cR
    ffn
    syl
    #
    prdsbasmpt
    mpbird
    eqeltrd
    #
    wph
    @6
    vx
    cB
    wph
    @1
    cB
    wcel
    #
    wa
    #
    @3
    @5
    @26
    vy
    cI
    @7
    c.0
    cfv
    #
    @7
    @1
    cfv
    #
    @8
    cplusg
    cfv
    #
    co
    #
    cmpt
    vy
    cI
    @28
    cmpt
    #
    @2
    @1
    @26
    vy
    cI
    @30
    @28
    @26
    @13
    wa
    #
    @30
    @9
    @28
    @29
    co
    #
    @28
    @32
    @27
    @9
    @28
    @29
    wph
    @13
    @27
    @9
    wceq
    @25
    @14
    @27
    @7
    @11
    cfv
    #
    @9
    @7
    c.0
    @11
    prdsidlem.z
    fveq1i
    wph
    @22
    @13
    @34
    @9
    wceq
    @23
    cI
    c0g
    cR
    @7
    fvco2
    sylan
    syl5eq
    adantlr
    #
    oveq1d
    @32
    @18
    @28
    @16
    wcel
    #
    @33
    @28
    wceq
    @26
    cI
    cmnd
    @7
    cR
    wph
    @21
    @25
    prdsplusgcl.r
    adantr
    ffvelrnda
    #
    @32
    cB
    cR
    cS
    @1
    cI
    @7
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    wph
    cS
    cV
    wcel
    #
    @25
    @13
    prdsplusgcl.s
    ad2antrr
    wph
    cI
    cW
    wcel
    #
    @25
    @13
    prdsplusgcl.i
    ad2antrr
    wph
    @22
    @25
    @13
    @23
    ad2antrr
    wph
    @25
    @13
    simplr
    @26
    @13
    simpr
    prdsbasprj
    #
    @16
    @29
    @8
    @28
    @9
    @19
    @29
    eqid
    #
    @20
    mndlid
    syl2anc
    eqtrd
    mpteq2dva
    @26
    vy
    cB
    c.pl
    cR
    cS
    c.0
    @1
    cI
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    wph
    @38
    @25
    prdsplusgcl.s
    adantr
    #
    wph
    @39
    @25
    prdsplusgcl.i
    adantr
    #
    wph
    @22
    @25
    @23
    adantr
    #
    wph
    @0
    @25
    @24
    adantr
    #
    wph
    @25
    simpr
    #
    prdsplusgcl.p
    prdsplusgval
    @26
    @1
    cI
    wfn
    @1
    @31
    wceq
    @26
    cB
    cR
    cS
    @1
    cI
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    @42
    @43
    @44
    @46
    prdsbasfn
    vy
    cI
    @1
    dffn5
    sylib
    #
    3eqtr4d
    @26
    vy
    cI
    @28
    @27
    @29
    co
    #
    cmpt
    @31
    @4
    @1
    @26
    vy
    cI
    @48
    @28
    @32
    @48
    @28
    @9
    @29
    co
    #
    @28
    @32
    @27
    @9
    @28
    @29
    @35
    oveq2d
    @32
    @18
    @36
    @49
    @28
    wceq
    @37
    @40
    @16
    @29
    @8
    @28
    @9
    @19
    @41
    @20
    mndrid
    syl2anc
    eqtrd
    mpteq2dva
    @26
    vy
    cB
    c.pl
    cR
    cS
    @1
    c.0
    cI
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    @42
    @43
    @44
    @46
    @45
    prdsplusgcl.p
    prdsplusgval
    @47
    3eqtr4d
    jca
    ralrimiva
    jca
end
