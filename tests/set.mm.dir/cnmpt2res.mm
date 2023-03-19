include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "ctx.mm"
include "co.mm"
include "crest.mm"
include "ccn.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "ctopon.mm"
include "cfv.mm"
include "wceq.mm"
include "txtopon.mm"
include "toponuni.mm"
include "syl.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cnrest.mm"
include "resmpt2.mm"
include "ctop.mm"
include "cvv.mm"
include "topontop.mm"
include "toponmax.mm"
include "ssexd.mm"
include "txrest.mm"
include "syl22anc.mm"
include "oveq12i.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "3eltr3d.mm"

theorem cnmpt2res
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cnmpt1res.2: |- K = ( J |`t Y )
  assume cnmpt1res.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt1res.5: |- ( ph -> Y C_ X )
  assume cnmpt2res.7: |- N = ( M |`t W )
  assume cnmpt2res.8: |- ( ph -> M e. ( TopOn ` Z ) )
  assume cnmpt2res.9: |- ( ph -> W C_ Z )
  assume cnmpt2res.10: |- ( ph -> ( x e. X , y e. Z |-> A ) e. ( ( J tX M ) Cn L ) )

  disjoint x y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( x e. Y , y e. W |-> A ) e. ( ( K tX N ) Cn L ) )

  proof
    wph
    vx
    vy
    cX
    cZ
    cA
    cmpt2
    #
    cY
    cW
    cxp
    #
    cres
    #
    cJ
    cM
    ctx
    co
    #
    @1
    crest
    co
    #
    cL
    ccn
    co
    #
    vx
    vy
    cY
    cW
    cA
    cmpt2
    #
    cK
    cN
    ctx
    co
    #
    cL
    ccn
    co
    wph
    @0
    @3
    cL
    ccn
    co
    wcel
    @1
    @3
    cuni
    #
    wss
    @2
    @5
    wcel
    cnmpt2res.10
    wph
    @1
    cX
    cZ
    cxp
    #
    @8
    wph
    cY
    cX
    wss
    #
    cW
    cZ
    wss
    #
    @1
    @9
    wss
    cnmpt1res.5
    cnmpt2res.9
    cY
    cX
    cW
    cZ
    xpss12
    syl2anc
    wph
    @3
    @9
    ctopon
    cfv
    wcel
    #
    @9
    @8
    wceq
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cM
    cZ
    ctopon
    cfv
    wcel
    #
    @12
    cnmpt1res.3
    cnmpt2res.8
    cJ
    cM
    cX
    cZ
    txtopon
    syl2anc
    @9
    @3
    toponuni
    syl
    sseqtrd
    @1
    @0
    @3
    cL
    @8
    @8
    eqid
    cnrest
    syl2anc
    wph
    @10
    @11
    @2
    @6
    wceq
    cnmpt1res.5
    cnmpt2res.9
    vx
    vy
    cX
    cZ
    cY
    cW
    cA
    resmpt2
    syl2anc
    wph
    @4
    @7
    cL
    ccn
    wph
    @4
    cJ
    cY
    crest
    co
    #
    cM
    cW
    crest
    co
    #
    ctx
    co
    #
    @7
    wph
    cJ
    ctop
    wcel
    #
    cM
    ctop
    wcel
    #
    cY
    cvv
    wcel
    cW
    cvv
    wcel
    @4
    @17
    wceq
    wph
    @13
    @18
    cnmpt1res.3
    cX
    cJ
    topontop
    syl
    wph
    @14
    @19
    cnmpt2res.8
    cZ
    cM
    topontop
    syl
    wph
    cY
    cX
    cJ
    wph
    @13
    cX
    cJ
    wcel
    cnmpt1res.3
    cX
    cJ
    toponmax
    syl
    cnmpt1res.5
    ssexd
    wph
    cW
    cZ
    cM
    wph
    @14
    cZ
    cM
    wcel
    cnmpt2res.8
    cZ
    cM
    toponmax
    syl
    cnmpt2res.9
    ssexd
    cY
    cW
    cJ
    cM
    ctop
    ctop
    cvv
    cvv
    txrest
    syl22anc
    cK
    @15
    cN
    @16
    ctx
    cnmpt1res.2
    cnmpt2res.7
    oveq12i
    syl6eqr
    oveq1d
    3eltr3d
end
