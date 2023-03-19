include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "ctps.mm"
include "cmt.mm"
include "mstps.mm"
include "syl.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "ovresd.mm"
include "mpteq2dva.mm"
include "ctx.mm"
include "msdcn.mm"
include "cnmpt12f.mm"
include "eqeltrrd.mm"

theorem cnmpt1ds
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume cnmpt1ds.d: |- D = ( dist ` G )
  assume cnmpt1ds.j: |- J = ( TopOpen ` G )
  assume cnmpt1ds.r: |- R = ( topGen ` ran (,) )
  assume cnmpt1ds.g: |- ( ph -> G e. MetSp )
  assume cnmpt1ds.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt1ds.a: |- ( ph -> ( x e. X |-> A ) e. ( K Cn J ) )
  assume cnmpt1ds.b: |- ( ph -> ( x e. X |-> B ) e. ( K Cn J ) )

  disjoint D x
  disjoint G x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint R x
  disjoint X x
  disjoint x y
  disjoint D y
  disjoint G y
  disjoint J y
  disjoint ph y
  disjoint R y
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X |-> ( A D B ) ) e. ( K Cn R ) )

  proof
    wph
    vx
    cX
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
    cmpt
    vx
    cX
    cA
    cB
    cD
    co
    #
    cmpt
    cK
    cR
    ccn
    co
    wph
    vx
    cX
    @2
    @3
    wph
    vx
    cv
    cX
    wcel
    wa
    cA
    cB
    cD
    @0
    wph
    cA
    @0
    wcel
    #
    vx
    cX
    wph
    cX
    @0
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @4
    vx
    cX
    wral
    wph
    cK
    cX
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
    @5
    cK
    cJ
    ccn
    co
    #
    wcel
    @6
    cnmpt1ds.k
    wph
    cG
    ctps
    wcel
    #
    @8
    wph
    cG
    cmt
    wcel
    #
    @10
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
    cnmpt1ds.a
    @5
    cK
    cJ
    cX
    @0
    cnf2
    syl3anc
    vx
    cX
    @0
    cA
    @5
    @5
    eqid
    fmpt
    sylibr
    r19.21bi
    wph
    cB
    @0
    wcel
    #
    vx
    cX
    wph
    cX
    @0
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @14
    vx
    cX
    wral
    wph
    @7
    @8
    @15
    @9
    wcel
    @16
    cnmpt1ds.k
    @13
    cnmpt1ds.b
    @15
    cK
    cJ
    cX
    @0
    cnf2
    syl3anc
    vx
    cX
    @0
    cB
    @15
    @15
    eqid
    fmpt
    sylibr
    r19.21bi
    ovresd
    mpteq2dva
    wph
    vx
    cA
    cB
    @1
    cK
    cJ
    cJ
    cR
    cX
    cnmpt1ds.k
    cnmpt1ds.a
    cnmpt1ds.b
    wph
    @11
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
    @12
    cnmpt1ds.d
    cnmpt1ds.j
    cnmpt1ds.r
    msdcn
    syl
    cnmpt12f
    eqeltrrd
end
