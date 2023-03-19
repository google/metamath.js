include "co.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cmap.mm"
include "crg.mm"
include "eqid.mm"
include "mamuval.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "syl.mm"
include "adantr.mm"
include "cfn.mm"
include "ad2antrr.mm"
include "wf.mm"
include "elmapi.mm"
include "simplrl.mm"
include "simpr.mm"
include "fovrnd.mm"
include "simplrr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "elmapg.mm"
include "sylancr.mm"
include "fmpt2.mm"
include "syl6rbbr.mm"
include "mpbid.mm"
include "eqeltrd.mm"

theorem mamucl
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume mamucl.b: |- B = ( Base ` R )
  assume mamucl.r: |- ( ph -> R e. Ring )
  assume mamucl.f: |- F = ( R maMul <. M , N , P >. )
  assume mamucl.m: |- ( ph -> M e. Fin )
  assume mamucl.n: |- ( ph -> N e. Fin )
  assume mamucl.p: |- ( ph -> P e. Fin )
  assume mamucl.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )
  assume mamucl.y: |- ( ph -> Y e. ( B ^m ( N X. P ) ) )


  assert |- ( ph -> ( X F Y ) e. ( B ^m ( M X. P ) ) )

  proof
    wph
    cX
    cY
    cF
    co
    vi
    vk
    cM
    cP
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
    vk
    cv
    #
    cY
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cmpt2
    #
    cB
    cM
    cP
    cxp
    #
    cmap
    co
    #
    wph
    cB
    cP
    cR
    @5
    vi
    vj
    vk
    cF
    cM
    cN
    crg
    cX
    cY
    mamucl.f
    mamucl.b
    @5
    eqid
    #
    mamucl.r
    mamucl.m
    mamucl.n
    mamucl.p
    mamucl.x
    mamucl.y
    mamuval
    wph
    @7
    cB
    wcel
    #
    vk
    cP
    wral
    vi
    cM
    wral
    #
    @8
    @10
    wcel
    #
    wph
    @12
    vi
    vk
    cM
    cP
    wph
    @0
    cM
    wcel
    #
    @3
    cP
    wcel
    #
    wa
    #
    wa
    #
    cB
    vj
    cR
    cN
    @6
    mamucl.b
    wph
    cR
    ccmn
    wcel
    #
    @17
    wph
    cR
    crg
    wcel
    #
    @19
    mamucl.r
    cR
    ringcmn
    syl
    adantr
    wph
    cN
    cfn
    wcel
    @17
    mamucl.n
    adantr
    @18
    @6
    cB
    wcel
    #
    vj
    cN
    @18
    @1
    cN
    wcel
    #
    wa
    #
    @20
    @2
    cB
    wcel
    @4
    cB
    wcel
    @21
    wph
    @20
    @17
    @22
    mamucl.r
    ad2antrr
    @23
    @0
    @1
    cB
    cM
    cN
    cX
    wph
    cM
    cN
    cxp
    #
    cB
    cX
    wf
    #
    @17
    @22
    wph
    cX
    cB
    @24
    cmap
    co
    wcel
    @25
    mamucl.x
    cX
    cB
    @24
    elmapi
    syl
    ad2antrr
    wph
    @15
    @16
    @22
    simplrl
    @18
    @22
    simpr
    #
    fovrnd
    @23
    @1
    @3
    cB
    cN
    cP
    cY
    wph
    cN
    cP
    cxp
    #
    cB
    cY
    wf
    #
    @17
    @22
    wph
    cY
    cB
    @27
    cmap
    co
    wcel
    @28
    mamucl.y
    cY
    cB
    @27
    elmapi
    syl
    ad2antrr
    @26
    wph
    @15
    @16
    @22
    simplrr
    fovrnd
    cB
    cR
    @5
    @2
    @4
    mamucl.b
    @11
    ringcl
    syl3anc
    ralrimiva
    gsummptcl
    ralrimivva
    wph
    @14
    @9
    cB
    @8
    wf
    #
    @13
    wph
    cB
    cvv
    wcel
    @9
    cfn
    wcel
    #
    @14
    @29
    wb
    cB
    cR
    cbs
    cfv
    cvv
    mamucl.b
    cR
    cbs
    fvex
    eqeltri
    wph
    cM
    cfn
    wcel
    cP
    cfn
    wcel
    @30
    mamucl.m
    mamucl.p
    cM
    cP
    xpfi
    syl2anc
    cB
    @9
    @8
    cvv
    cfn
    elmapg
    sylancr
    vi
    vk
    cM
    cP
    @7
    cB
    @8
    @8
    eqid
    fmpt2
    syl6rbbr
    mpbid
    eqeltrd
end
