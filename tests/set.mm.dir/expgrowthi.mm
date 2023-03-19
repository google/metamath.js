include "cdv.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "ce.mm"
include "cfv.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "cc.mm"
include "cr.mm"
include "cpr.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "eleq2.mm"
include "recn.mm"
include "syl6bi.mm"
include "biimpd.mm"
include "jaoi.mm"
include "3syl.mm"
include "imp.mm"
include "wa.mm"
include "mulcl.mm"
include "sylan.mm"
include "efcl.mm"
include "syl.mm"
include "syldan.mm"
include "ovexd.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "adantr.mm"
include "adantl.mm"
include "c1.mm"
include "1cnd.mm"
include "dvmptid.mm"
include "dvmptcmul.mm"
include "mulid1d.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "dvef.mm"
include "wfn.mm"
include "wf.mm"
include "eff.mm"
include "ffn.mm"
include "ax-mp.mm"
include "dffn5.mm"
include "mpbi.mm"
include "3eqtr3i.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "mulcom.mm"
include "syl2anr.mm"
include "anabss5.mm"
include "mpteq2dva.mm"
include "w3a.mm"
include "3anim123i.mm"
include "3anidm12.mm"
include "mul12.mm"
include "syl5eq.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "eqtr4d.mm"

theorem expgrowthi
  let wph: wff ph
  let vt: setvar t
  let cC: class C
  let cS: class S
  let cK: class K
  let cY: class Y
  let vy: setvar y
  let vx: setvar x
  assume expgrowthi.s: |- ( ph -> S e. { RR , CC } )
  assume expgrowthi.k: |- ( ph -> K e. CC )
  assume expgrowthi.y0: |- ( ph -> C e. CC )
  assume expgrowthi.yt: |- Y = ( t e. S |-> ( C x. ( exp ` ( K x. t ) ) ) )

  disjoint C t
  disjoint K t
  disjoint S t
  disjoint t y
  disjoint C y
  disjoint K y
  disjoint S y
  disjoint x y
  disjoint K x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( S _D Y ) = ( ( S X. { K } ) oF x. Y ) )

  proof
    wph
    cS
    cY
    cdv
    co
    #
    vy
    cS
    cK
    cC
    cK
    vy
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmpt
    #
    cS
    cK
    csn
    cxp
    #
    cY
    cmul
    cof
    co
    wph
    @0
    cS
    vy
    cS
    @4
    cmpt
    #
    cdv
    co
    #
    @6
    cY
    @8
    cS
    cdv
    cY
    vt
    cS
    cC
    cK
    vt
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cmpt
    @8
    expgrowthi.yt
    vt
    vy
    cS
    @13
    @4
    @10
    @1
    wceq
    #
    @12
    @3
    cC
    cmul
    @14
    @11
    @2
    ce
    @10
    @1
    cK
    cmul
    oveq2
    fveq2d
    oveq2d
    cbvmptv
    eqtri
    #
    oveq2i
    wph
    @9
    vy
    cS
    cC
    cK
    @3
    cmul
    co
    #
    cmul
    co
    #
    cmpt
    @6
    wph
    vy
    @3
    @16
    cC
    cS
    cvv
    cS
    expgrowthi.s
    wph
    @1
    cS
    wcel
    #
    @1
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    wph
    @18
    @19
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    cS
    cr
    wceq
    #
    cS
    cc
    wceq
    #
    wo
    @18
    @19
    wi
    #
    expgrowthi.s
    cS
    cr
    cc
    elpri
    @22
    @24
    @23
    @22
    @18
    @1
    cr
    wcel
    @19
    cS
    cr
    @1
    eleq2
    @1
    recn
    syl6bi
    @23
    @18
    @19
    cS
    cc
    @1
    eleq2
    biimpd
    jaoi
    3syl
    imp
    #
    wph
    @19
    wa
    @2
    cc
    wcel
    #
    @20
    wph
    cK
    cc
    wcel
    #
    @19
    @26
    expgrowthi.k
    cK
    @1
    mulcl
    sylan
    #
    @2
    efcl
    syl
    syldan
    #
    wph
    @18
    wa
    #
    cK
    @3
    cmul
    ovexd
    wph
    cS
    vy
    cS
    @3
    cmpt
    cdv
    co
    vy
    cS
    @3
    cK
    cmul
    co
    #
    cmpt
    vy
    cS
    @16
    cmpt
    wph
    vy
    vx
    @2
    cK
    vx
    cv
    #
    ce
    cfv
    #
    @33
    cS
    cc
    @3
    @3
    cc
    cc
    cS
    cc
    expgrowthi.s
    cc
    @21
    wcel
    wph
    cnelprrecn
    a1i
    wph
    @18
    @19
    @26
    @25
    @28
    syldan
    wph
    @27
    @18
    expgrowthi.k
    adantr
    #
    @32
    cc
    wcel
    @33
    cc
    wcel
    wph
    @32
    efcl
    adantl
    #
    @35
    wph
    cS
    vy
    cS
    @2
    cmpt
    cdv
    co
    vy
    cS
    cK
    c1
    cmul
    co
    #
    cmpt
    vy
    cS
    cK
    cmpt
    #
    wph
    vy
    @1
    c1
    cK
    cS
    cc
    cS
    expgrowthi.s
    @25
    @30
    1cnd
    wph
    vy
    cS
    expgrowthi.s
    dvmptid
    expgrowthi.k
    dvmptcmul
    wph
    vy
    cS
    @36
    cK
    wph
    cK
    expgrowthi.k
    mulid1d
    mpteq2dv
    eqtrd
    cc
    vx
    cc
    @33
    cmpt
    #
    cdv
    co
    #
    @38
    wceq
    wph
    cc
    ce
    cdv
    co
    ce
    @39
    @38
    dvef
    ce
    @38
    cc
    cdv
    ce
    cc
    wfn
    #
    ce
    @38
    wceq
    cc
    cc
    ce
    wf
    @40
    eff
    cc
    cc
    ce
    ffn
    ax-mp
    vx
    cc
    ce
    dffn5
    mpbi
    #
    oveq2i
    @41
    3eqtr3i
    a1i
    @32
    @2
    ce
    fveq2
    #
    @42
    dvmptco
    wph
    vy
    cS
    @31
    @16
    wph
    @18
    @31
    @16
    wceq
    #
    @30
    @20
    @27
    @43
    wph
    @29
    expgrowthi.k
    @3
    cK
    mulcom
    syl2anr
    anabss5
    mpteq2dva
    eqtrd
    expgrowthi.y0
    dvmptcmul
    wph
    vy
    cS
    @17
    @5
    @30
    cC
    cc
    wcel
    #
    @27
    @20
    w3a
    #
    @17
    @5
    wceq
    wph
    @18
    @45
    wph
    @30
    @45
    wph
    @44
    wph
    @27
    @30
    @20
    expgrowthi.y0
    expgrowthi.k
    @29
    3anim123i
    3anidm12
    anabss5
    cC
    cK
    @3
    mul12
    syl
    mpteq2dva
    eqtrd
    syl5eq
    wph
    vy
    cS
    cK
    @4
    cmul
    @7
    cY
    @21
    cc
    cvv
    expgrowthi.s
    @34
    @30
    cC
    @3
    cmul
    ovexd
    @7
    @37
    wceq
    wph
    vy
    cS
    cK
    fconstmpt
    a1i
    cY
    @8
    wceq
    wph
    @15
    a1i
    offval2
    eqtr4d
end
