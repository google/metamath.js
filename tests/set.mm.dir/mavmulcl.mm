include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmap.mm"
include "crg.mm"
include "mavmulval.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "syl.mm"
include "adantr.mm"
include "cfn.mm"
include "ad2antrr.mm"
include "cxp.mm"
include "wf.mm"
include "cbs.mm"
include "wceq.mm"
include "matbas2.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "elmapi.mm"
include "simpr.mm"
include "fovrnd.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "sylancr.mm"
include "eqid.mm"
include "fmpt.mm"
include "syl6rbbr.mm"
include "mpbid.mm"
include "eqeltrd.mm"

theorem mavmulcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cN: class N
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  assume mavmulcl.a: |- A = ( N Mat R )
  assume mavmulcl.m: |- .X. = ( R maVecMul <. N , N >. )
  assume mavmulcl.b: |- B = ( Base ` R )
  assume mavmulcl.t: |- .x. = ( .r ` R )
  assume mavmulcl.r: |- ( ph -> R e. Ring )
  assume mavmulcl.n: |- ( ph -> N e. Fin )
  assume mavmulcl.x: |- ( ph -> X e. ( Base ` A ) )
  assume mavmulcl.y: |- ( ph -> Y e. ( B ^m N ) )


  assert |- ( ph -> ( X .X. Y ) e. ( B ^m N ) )

  proof
    wph
    cX
    cY
    c.xp
    co
    vi
    cN
    cR
    vj
    cN
    vi
    cv
    #
    vj
    cv
    #
    cX
    co
    #
    @1
    cY
    cfv
    #
    c.x
    co
    #
    cmpt
    cgsu
    co
    #
    cmpt
    #
    cB
    cN
    cmap
    co
    #
    wph
    cA
    cB
    cR
    c.x
    c.xp
    vi
    vj
    cN
    crg
    cX
    cY
    mavmulcl.a
    mavmulcl.m
    mavmulcl.b
    mavmulcl.t
    mavmulcl.r
    mavmulcl.n
    mavmulcl.x
    mavmulcl.y
    mavmulval
    wph
    @5
    cB
    wcel
    #
    vi
    cN
    wral
    #
    @6
    @7
    wcel
    #
    wph
    @8
    vi
    cN
    wph
    @0
    cN
    wcel
    #
    wa
    #
    cB
    vj
    cR
    cN
    @4
    mavmulcl.b
    wph
    cR
    ccmn
    wcel
    #
    @11
    wph
    cR
    crg
    wcel
    #
    @13
    mavmulcl.r
    cR
    ringcmn
    syl
    adantr
    wph
    cN
    cfn
    wcel
    #
    @11
    mavmulcl.n
    adantr
    @12
    @4
    cB
    wcel
    #
    vj
    cN
    @12
    @1
    cN
    wcel
    #
    wa
    #
    @14
    @2
    cB
    wcel
    @3
    cB
    wcel
    @16
    wph
    @14
    @11
    @17
    mavmulcl.r
    ad2antrr
    @18
    @0
    @1
    cB
    cN
    cN
    cX
    wph
    cN
    cN
    cxp
    #
    cB
    cX
    wf
    #
    @11
    @17
    wph
    cX
    cB
    @19
    cmap
    co
    #
    wcel
    @20
    wph
    cX
    cA
    cbs
    cfv
    #
    @21
    mavmulcl.x
    wph
    @15
    @14
    @21
    @22
    wceq
    mavmulcl.n
    mavmulcl.r
    cA
    cR
    cB
    cN
    crg
    mavmulcl.a
    mavmulcl.b
    matbas2
    syl2anc
    eleqtrrd
    cX
    cB
    @19
    elmapi
    syl
    ad2antrr
    @12
    @11
    @17
    wph
    @11
    simpr
    adantr
    @12
    @17
    simpr
    #
    fovrnd
    @18
    cN
    cB
    @1
    cY
    wph
    cN
    cB
    cY
    wf
    #
    @11
    @17
    wph
    cY
    @7
    wcel
    @24
    mavmulcl.y
    cY
    cB
    cN
    elmapi
    syl
    ad2antrr
    @23
    ffvelrnd
    cB
    cR
    c.x
    @2
    @3
    mavmulcl.b
    mavmulcl.t
    ringcl
    syl3anc
    ralrimiva
    gsummptcl
    ralrimiva
    wph
    @10
    cN
    cB
    @6
    wf
    #
    @9
    wph
    cB
    cvv
    wcel
    @15
    @10
    @25
    wb
    cB
    cR
    cbs
    cfv
    cvv
    mavmulcl.b
    cR
    cbs
    fvex
    eqeltri
    mavmulcl.n
    cB
    cN
    @6
    cvv
    cfn
    elmapg
    sylancr
    vi
    cN
    cB
    @5
    @6
    @6
    eqid
    fmpt
    syl6rbbr
    mpbid
    eqeltrd
end
