include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "clt.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cmulr.mm"
include "eqid.mm"
include "adantr.mm"
include "simpr.mm"
include "mplvscaval.mm"
include "adantrr.mm"
include "simprl.mm"
include "simprr.mm"
include "mdeglt.mm"
include "oveq2d.mm"
include "crg.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "wb.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "mpllmod.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mdegxrcl.mm"
include "syl.mm"
include "mdegleb.mm"
include "mpbird.mm"

theorem mdegvscale
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  assume mdegaddle.y: |- Y = ( I mPoly R )
  assume mdegaddle.d: |- D = ( I mDeg R )
  assume mdegaddle.i: |- ( ph -> I e. V )
  assume mdegaddle.r: |- ( ph -> R e. Ring )
  assume mdegvscale.b: |- B = ( Base ` Y )
  assume mdegvscale.k: |- K = ( Base ` R )
  assume mdegvscale.p: |- .x. = ( .s ` Y )
  assume mdegvscale.f: |- ( ph -> F e. K )
  assume mdegvscale.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .x. G ) ) <_ ( D ` G ) )

  proof
    wph
    cF
    cG
    c.x
    co
    #
    cD
    cfv
    cG
    cD
    cfv
    #
    cle
    wbr
    #
    @1
    vx
    cv
    #
    vb
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    va
    cn0
    cI
    cmap
    co
    crab
    #
    ccnfld
    vb
    cv
    cgsu
    co
    cmpt
    #
    cfv
    clt
    wbr
    #
    @3
    @0
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vx
    @4
    wral
    #
    wph
    @10
    vx
    @4
    wph
    @3
    @4
    wcel
    #
    @6
    @9
    wph
    @12
    @6
    wa
    #
    wa
    #
    @7
    cF
    @3
    cG
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    @8
    @16
    co
    #
    @8
    wph
    @12
    @7
    @17
    wceq
    @6
    wph
    @12
    wa
    cB
    @4
    cY
    cR
    c.x
    @16
    va
    cG
    cI
    cK
    cF
    @3
    mdegaddle.y
    mdegvscale.p
    mdegvscale.k
    mdegvscale.b
    @16
    eqid
    #
    @4
    eqid
    #
    wph
    cF
    cK
    wcel
    #
    @12
    mdegvscale.f
    adantr
    wph
    cG
    cB
    wcel
    #
    @12
    mdegvscale.g
    adantr
    wph
    @12
    simpr
    mplvscaval
    adantrr
    @14
    @15
    @8
    cF
    @16
    @14
    @4
    cB
    cD
    cY
    cR
    vb
    va
    cG
    @5
    cI
    @3
    @8
    mdegaddle.d
    mdegaddle.y
    mdegvscale.b
    @8
    eqid
    #
    @20
    @5
    eqid
    #
    wph
    @22
    @13
    mdegvscale.g
    adantr
    wph
    @12
    @6
    simprl
    wph
    @12
    @6
    simprr
    mdeglt
    oveq2d
    wph
    @18
    @8
    wceq
    #
    @13
    wph
    cR
    crg
    wcel
    #
    @21
    @25
    mdegaddle.r
    mdegvscale.f
    cK
    cR
    @16
    cF
    @8
    mdegvscale.k
    @19
    @23
    ringrz
    syl2anc
    adantr
    3eqtrd
    expr
    ralrimiva
    wph
    @0
    cB
    wcel
    #
    @1
    cxr
    wcel
    #
    @2
    @11
    wb
    wph
    cY
    clmod
    wcel
    #
    cF
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @22
    @27
    wph
    cI
    cV
    wcel
    @26
    @29
    mdegaddle.i
    mdegaddle.r
    cY
    cR
    cI
    cV
    mdegaddle.y
    mpllmod
    syl2anc
    wph
    cF
    cK
    @31
    mdegvscale.f
    wph
    cK
    cR
    cbs
    cfv
    @31
    mdegvscale.k
    wph
    cR
    @30
    cbs
    wph
    cY
    cR
    cI
    cV
    crg
    mdegaddle.y
    mdegaddle.i
    mdegaddle.r
    mplsca
    fveq2d
    syl5eq
    eleqtrd
    mdegvscale.g
    cF
    c.x
    @30
    @31
    cB
    cY
    cG
    mdegvscale.b
    @30
    eqid
    mdegvscale.p
    @31
    eqid
    lmodvscl
    syl3anc
    wph
    @22
    @28
    mdegvscale.g
    cB
    cD
    cY
    cR
    cG
    cI
    mdegaddle.d
    mdegaddle.y
    mdegvscale.b
    mdegxrcl
    syl
    vx
    @4
    cB
    cD
    cY
    cR
    vb
    va
    @0
    @1
    @5
    cI
    @8
    mdegaddle.d
    mdegaddle.y
    mdegvscale.b
    @23
    @20
    @24
    mdegleb
    syl2anc
    mpbird
end
