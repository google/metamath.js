include "cscaf.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wceq.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "ctps.mm"
include "ctlm.mm"
include "tlmscatps.mm"
include "syl.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "tlmtps.mm"
include "scafval.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "ctx.mm"
include "vscacn.mm"
include "cnmpt12f.mm"
include "eqeltrrd.mm"

theorem cnmpt1vsca
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume tlmtrg.f: |- F = ( Scalar ` W )
  assume cnmpt1vsca.t: |- .x. = ( .s ` W )
  assume cnmpt1vsca.j: |- J = ( TopOpen ` W )
  assume cnmpt1vsca.k: |- K = ( TopOpen ` F )
  assume cnmpt1vsca.w: |- ( ph -> W e. TopMod )
  assume cnmpt1vsca.l: |- ( ph -> L e. ( TopOn ` X ) )
  assume cnmpt1vsca.a: |- ( ph -> ( x e. X |-> A ) e. ( L Cn K ) )
  assume cnmpt1vsca.b: |- ( ph -> ( x e. X |-> B ) e. ( L Cn J ) )

  disjoint F x
  disjoint J x
  disjoint K x
  disjoint L x
  disjoint ph x
  disjoint W x
  disjoint X x
  disjoint x y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint ph y
  disjoint W y
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X |-> ( A .x. B ) ) e. ( L Cn J ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cW
    cscaf
    cfv
    #
    co
    #
    cmpt
    vx
    cX
    cA
    cB
    c.x
    co
    #
    cmpt
    cL
    cJ
    ccn
    co
    #
    wph
    vx
    cX
    @1
    @2
    wph
    vx
    cv
    cX
    wcel
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
    @1
    @2
    wceq
    wph
    @5
    vx
    cX
    wph
    cX
    @4
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @5
    vx
    cX
    wral
    wph
    cL
    cX
    ctopon
    cfv
    wcel
    #
    cK
    @4
    ctopon
    cfv
    wcel
    #
    @8
    cL
    cK
    ccn
    co
    wcel
    @9
    cnmpt1vsca.l
    wph
    cF
    ctps
    wcel
    #
    @11
    wph
    cW
    ctlm
    wcel
    #
    @12
    cnmpt1vsca.w
    cF
    cW
    tlmtrg.f
    tlmscatps
    syl
    @4
    cK
    cF
    @4
    eqid
    #
    cnmpt1vsca.k
    istps
    sylib
    cnmpt1vsca.a
    @8
    cL
    cK
    cX
    @4
    cnf2
    syl3anc
    vx
    cX
    @4
    cA
    @8
    @8
    eqid
    fmpt
    sylibr
    r19.21bi
    wph
    @7
    vx
    cX
    wph
    cX
    @6
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @7
    vx
    cX
    wral
    wph
    @10
    cJ
    @6
    ctopon
    cfv
    wcel
    #
    @15
    @3
    wcel
    @16
    cnmpt1vsca.l
    wph
    cW
    ctps
    wcel
    #
    @17
    wph
    @13
    @18
    cnmpt1vsca.w
    cW
    tlmtps
    syl
    @6
    cJ
    cW
    @6
    eqid
    #
    cnmpt1vsca.j
    istps
    sylib
    cnmpt1vsca.b
    @15
    cL
    cJ
    cX
    @6
    cnf2
    syl3anc
    vx
    cX
    @6
    cB
    @15
    @15
    eqid
    fmpt
    sylibr
    r19.21bi
    @6
    @0
    c.x
    cF
    @4
    cW
    cA
    cB
    @19
    tlmtrg.f
    @14
    @0
    eqid
    #
    cnmpt1vsca.t
    scafval
    syl2anc
    mpteq2dva
    wph
    vx
    cA
    cB
    @0
    cL
    cK
    cJ
    cJ
    cX
    cnmpt1vsca.l
    cnmpt1vsca.a
    cnmpt1vsca.b
    wph
    @13
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
    @20
    cnmpt1vsca.j
    tlmtrg.f
    cnmpt1vsca.k
    vscacn
    syl
    cnmpt12f
    eqeltrrd
end
