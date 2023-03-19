include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "c0g.mm"
include "cfv.mm"
include "csupp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "cbs.mm"
include "eqid.mm"
include "rrgss.mm"
include "sseldi.mm"
include "mplvsca.mm"
include "oveq1d.mm"
include "cvv.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "mplelf.mm"
include "rrgsupp.mm"
include "eqtrd.mm"
include "imaeq2d.mm"
include "supeq1d.mm"
include "wceq.mm"
include "clmod.mm"
include "csca.mm"
include "crg.mm"
include "mpllmod.mm"
include "syl2anc.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mdegval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem mdegvsca
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mdegaddle.y: |- Y = ( I mPoly R )
  assume mdegaddle.d: |- D = ( I mDeg R )
  assume mdegaddle.i: |- ( ph -> I e. V )
  assume mdegaddle.r: |- ( ph -> R e. Ring )
  assume mdegvsca.b: |- B = ( Base ` Y )
  assume mdegvsca.e: |- E = ( RLReg ` R )
  assume mdegvsca.p: |- .x. = ( .s ` Y )
  assume mdegvsca.f: |- ( ph -> F e. E )
  assume mdegvsca.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .x. G ) ) = ( D ` G ) )

  proof
    wph
    vy
    vx
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vx
    cn0
    cI
    cmap
    co
    #
    crab
    #
    ccnfld
    vy
    cv
    cgsu
    co
    cmpt
    #
    cF
    cG
    c.x
    co
    #
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    @3
    cG
    @5
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    @4
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    wph
    cxr
    @7
    @10
    clt
    wph
    @6
    @9
    @3
    wph
    @6
    @2
    cF
    csn
    cxp
    cG
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    @5
    csupp
    co
    @9
    wph
    @4
    @15
    @5
    csupp
    wph
    cB
    @2
    cY
    cR
    c.x
    @14
    vx
    cG
    cI
    cR
    cbs
    cfv
    #
    cF
    mdegaddle.y
    mdegvsca.p
    @16
    eqid
    #
    mdegvsca.b
    @14
    eqid
    #
    @2
    eqid
    #
    wph
    cE
    @16
    cF
    @16
    cR
    cE
    mdegvsca.e
    @17
    rrgss
    mdegvsca.f
    sseldi
    #
    mdegvsca.g
    mplvsca
    oveq1d
    wph
    @16
    cR
    @14
    cE
    @2
    cvv
    cF
    cG
    @5
    mdegvsca.e
    @17
    @18
    @5
    eqid
    #
    @2
    cvv
    wcel
    wph
    @0
    vx
    @1
    cn0
    cI
    cmap
    ovex
    rabex
    a1i
    mdegaddle.r
    mdegvsca.f
    wph
    cB
    @2
    cY
    cR
    vx
    cI
    @16
    cG
    mdegaddle.y
    @17
    mdegvsca.b
    @19
    mdegvsca.g
    mplelf
    rrgsupp
    eqtrd
    imaeq2d
    supeq1d
    wph
    @4
    cB
    wcel
    #
    @12
    @8
    wceq
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
    cG
    cB
    wcel
    #
    @22
    wph
    cI
    cV
    wcel
    cR
    crg
    wcel
    @23
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
    @16
    @25
    @20
    wph
    cR
    @24
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
    eleqtrd
    mdegvsca.g
    cF
    c.x
    @24
    @25
    cB
    cY
    cG
    mdegvsca.b
    @24
    eqid
    mdegvsca.p
    @25
    eqid
    lmodvscl
    syl3anc
    @2
    cB
    cD
    cY
    cR
    vy
    vx
    @4
    @3
    cI
    @5
    mdegaddle.d
    mdegaddle.y
    mdegvsca.b
    @21
    @19
    @3
    eqid
    #
    mdegval
    syl
    wph
    @26
    @13
    @11
    wceq
    mdegvsca.g
    @2
    cB
    cD
    cY
    cR
    vy
    vx
    cG
    @3
    cI
    @5
    mdegaddle.d
    mdegaddle.y
    mdegvsca.b
    @21
    @19
    @27
    mdegval
    syl
    3eqtr4d
end
