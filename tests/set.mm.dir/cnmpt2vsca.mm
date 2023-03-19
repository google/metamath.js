include "cscaf.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "ctopon.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctps.mm"
include "ctlm.mm"
include "tlmscatps.mm"
include "syl.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "tlmtps.mm"
include "scafval.mm"
include "3impa.mm"
include "mpt2eq3dva.mm"
include "vscacn.mm"
include "cnmpt22f.mm"
include "eqeltrrd.mm"

theorem cnmpt2vsca
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume tlmtrg.f: |- F = ( Scalar ` W )
  assume cnmpt1vsca.t: |- .x. = ( .s ` W )
  assume cnmpt1vsca.j: |- J = ( TopOpen ` W )
  assume cnmpt1vsca.k: |- K = ( TopOpen ` F )
  assume cnmpt1vsca.w: |- ( ph -> W e. TopMod )
  assume cnmpt1vsca.l: |- ( ph -> L e. ( TopOn ` X ) )
  assume cnmpt2vsca.m: |- ( ph -> M e. ( TopOn ` Y ) )
  assume cnmpt2vsca.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( L tX M ) Cn K ) )
  assume cnmpt2vsca.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( L tX M ) Cn J ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X , y e. Y |-> ( A .x. B ) ) e. ( ( L tX M ) Cn J ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cA
    cB
    cW
    cscaf
    cfv
    #
    co
    #
    cmpt2
    vx
    vy
    cX
    cY
    cA
    cB
    c.x
    co
    #
    cmpt2
    cL
    cM
    ctx
    co
    #
    cJ
    ccn
    co
    #
    wph
    vx
    vy
    cX
    cY
    @1
    @2
    wph
    vx
    cv
    cX
    wcel
    #
    vy
    cv
    cY
    wcel
    #
    @1
    @2
    wceq
    #
    wph
    @5
    wa
    #
    @6
    wa
    cA
    cF
    cbs
    cfv
    #
    wcel
    #
    cB
    cW
    cbs
    cfv
    #
    wcel
    #
    @7
    @8
    @10
    vy
    cY
    wph
    @10
    vy
    cY
    wral
    #
    vx
    cX
    wph
    cX
    cY
    cxp
    #
    @9
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    wf
    #
    @13
    vx
    cX
    wral
    wph
    @3
    @14
    ctopon
    cfv
    wcel
    #
    cK
    @9
    ctopon
    cfv
    wcel
    #
    @15
    @3
    cK
    ccn
    co
    wcel
    @16
    wph
    cL
    cX
    ctopon
    cfv
    wcel
    cM
    cY
    ctopon
    cfv
    wcel
    @17
    cnmpt1vsca.l
    cnmpt2vsca.m
    cL
    cM
    cX
    cY
    txtopon
    syl2anc
    #
    wph
    cF
    ctps
    wcel
    #
    @18
    wph
    cW
    ctlm
    wcel
    #
    @20
    cnmpt1vsca.w
    cF
    cW
    tlmtrg.f
    tlmscatps
    syl
    @9
    cK
    cF
    @9
    eqid
    #
    cnmpt1vsca.k
    istps
    sylib
    cnmpt2vsca.a
    @15
    @3
    cK
    @14
    @9
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cA
    @9
    @15
    @15
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    @8
    @12
    vy
    cY
    wph
    @12
    vy
    cY
    wral
    #
    vx
    cX
    wph
    @14
    @11
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    wf
    #
    @23
    vx
    cX
    wral
    wph
    @17
    cJ
    @11
    ctopon
    cfv
    wcel
    #
    @24
    @4
    wcel
    @25
    @19
    wph
    cW
    ctps
    wcel
    #
    @26
    wph
    @21
    @27
    cnmpt1vsca.w
    cW
    tlmtps
    syl
    @11
    cJ
    cW
    @11
    eqid
    #
    cnmpt1vsca.j
    istps
    sylib
    cnmpt2vsca.b
    @24
    @3
    cJ
    @14
    @11
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cB
    @11
    @24
    @24
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    @11
    @0
    c.x
    cF
    @9
    cW
    cA
    cB
    @28
    tlmtrg.f
    @22
    @0
    eqid
    #
    cnmpt1vsca.t
    scafval
    syl2anc
    3impa
    mpt2eq3dva
    wph
    vx
    vy
    cA
    cB
    @0
    cL
    cM
    cK
    cJ
    cJ
    cX
    cY
    cnmpt1vsca.l
    cnmpt2vsca.m
    cnmpt2vsca.a
    cnmpt2vsca.b
    wph
    @21
    @0
    cK
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    cnmpt1vsca.w
    @0
    cF
    cJ
    cK
    cW
    @29
    cnmpt1vsca.j
    tlmtrg.f
    cnmpt1vsca.k
    vscacn
    syl
    cnmpt22f
    eqeltrrd
end
