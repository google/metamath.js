include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wf.mm"
include "ctopon.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctps.mm"
include "cmt.mm"
include "mstps.mm"
include "syl.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "ovresd.mm"
include "3impa.mm"
include "mpt2eq3dva.mm"
include "msdcn.mm"
include "cnmpt22f.mm"
include "eqeltrrd.mm"

theorem cnmpt2ds
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  assume cnmpt1ds.d: |- D = ( dist ` G )
  assume cnmpt1ds.j: |- J = ( TopOpen ` G )
  assume cnmpt1ds.r: |- R = ( topGen ` ran (,) )
  assume cnmpt1ds.g: |- ( ph -> G e. MetSp )
  assume cnmpt1ds.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt2ds.l: |- ( ph -> L e. ( TopOn ` Y ) )
  assume cnmpt2ds.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( K tX L ) Cn J ) )
  assume cnmpt2ds.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( K tX L ) Cn J ) )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G x
  disjoint G y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X , y e. Y |-> ( A D B ) ) e. ( ( K tX L ) Cn R ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cA
    cB
    cD
    cG
    cbs
    cfv
    #
    @0
    cxp
    cres
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
    cD
    co
    #
    cmpt2
    cK
    cL
    ctx
    co
    #
    cR
    ccn
    co
    wph
    vx
    vy
    cX
    cY
    @2
    @3
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
    @2
    @3
    wceq
    wph
    @5
    wa
    #
    @6
    wa
    cA
    cB
    cD
    @0
    @7
    cA
    @0
    wcel
    #
    vy
    cY
    wph
    @8
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
    @0
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    wf
    #
    @9
    vx
    cX
    wral
    wph
    @4
    @10
    ctopon
    cfv
    wcel
    #
    cJ
    @0
    ctopon
    cfv
    wcel
    #
    @11
    @4
    cJ
    ccn
    co
    #
    wcel
    @12
    wph
    cK
    cX
    ctopon
    cfv
    wcel
    cL
    cY
    ctopon
    cfv
    wcel
    @13
    cnmpt1ds.k
    cnmpt2ds.l
    cK
    cL
    cX
    cY
    txtopon
    syl2anc
    #
    wph
    cG
    ctps
    wcel
    #
    @14
    wph
    cG
    cmt
    wcel
    #
    @17
    cnmpt1ds.g
    cG
    mstps
    syl
    @0
    cJ
    cG
    @0
    eqid
    #
    cnmpt1ds.j
    istps
    sylib
    #
    cnmpt2ds.a
    @11
    @4
    cJ
    @10
    @0
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cA
    @0
    @11
    @11
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    @7
    cB
    @0
    wcel
    #
    vy
    cY
    wph
    @21
    vy
    cY
    wral
    #
    vx
    cX
    wph
    @10
    @0
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    wf
    #
    @22
    vx
    cX
    wral
    wph
    @13
    @14
    @23
    @15
    wcel
    @24
    @16
    @20
    cnmpt2ds.b
    @23
    @4
    cJ
    @10
    @0
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cB
    @0
    @23
    @23
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    ovresd
    3impa
    mpt2eq3dva
    wph
    vx
    vy
    cA
    cB
    @1
    cK
    cL
    cJ
    cJ
    cR
    cX
    cY
    cnmpt1ds.k
    cnmpt2ds.l
    cnmpt2ds.a
    cnmpt2ds.b
    wph
    @18
    @1
    cJ
    cJ
    ctx
    co
    cR
    ccn
    co
    wcel
    cnmpt1ds.g
    cD
    cJ
    cR
    cG
    @0
    @19
    cnmpt1ds.d
    cnmpt1ds.j
    cnmpt1ds.r
    msdcn
    syl
    cnmpt22f
    eqeltrrd
end
