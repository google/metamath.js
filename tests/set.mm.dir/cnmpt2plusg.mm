include "cplusf.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cbs.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "ctopon.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctmd.mm"
include "eqid.mm"
include "tmdtopon.mm"
include "syl.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "3impa.mm"
include "plusfval.mm"
include "mpt2eq3dva.mm"
include "tmdcn.mm"
include "cnmpt22f.mm"
include "eqeltrrd.mm"

theorem cnmpt2plusg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume cnmpt1plusg.p: |- .+ = ( +g ` G )
  assume cnmpt1plusg.g: |- ( ph -> G e. TopMnd )
  assume cnmpt1plusg.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt2plusg.l: |- ( ph -> L e. ( TopOn ` Y ) )
  assume cnmpt2plusg.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( K tX L ) Cn J ) )
  assume cnmpt2plusg.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( K tX L ) Cn J ) )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X , y e. Y |-> ( A .+ B ) ) e. ( ( K tX L ) Cn J ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cA
    cB
    cG
    cplusf
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
    c.pl
    co
    #
    cmpt2
    cK
    cL
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
    w3a
    cA
    cG
    cbs
    cfv
    #
    wcel
    #
    cB
    @7
    wcel
    #
    @1
    @2
    wceq
    wph
    @5
    @6
    @8
    wph
    @5
    wa
    #
    @8
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
    @7
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    wf
    #
    @11
    vx
    cX
    wral
    wph
    @3
    @12
    ctopon
    cfv
    wcel
    #
    cJ
    @7
    ctopon
    cfv
    wcel
    #
    @13
    @4
    wcel
    @14
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
    @15
    cnmpt1plusg.k
    cnmpt2plusg.l
    cK
    cL
    cX
    cY
    txtopon
    syl2anc
    #
    wph
    cG
    ctmd
    wcel
    #
    @16
    cnmpt1plusg.g
    cG
    cJ
    @7
    tgpcn.j
    @7
    eqid
    #
    tmdtopon
    syl
    #
    cnmpt2plusg.a
    @13
    @3
    cJ
    @12
    @7
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cA
    @7
    @13
    @13
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    3impa
    wph
    @5
    @6
    @9
    @10
    @9
    vy
    cY
    wph
    @9
    vy
    cY
    wral
    #
    vx
    cX
    wph
    @12
    @7
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    wf
    #
    @21
    vx
    cX
    wral
    wph
    @15
    @16
    @22
    @4
    wcel
    @23
    @17
    @20
    cnmpt2plusg.b
    @22
    @3
    cJ
    @12
    @7
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cB
    @7
    @22
    @22
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    3impa
    @7
    c.pl
    @0
    cG
    cA
    cB
    @19
    cnmpt1plusg.p
    @0
    eqid
    #
    plusfval
    syl2anc
    mpt2eq3dva
    wph
    vx
    vy
    cA
    cB
    @0
    cK
    cL
    cJ
    cJ
    cJ
    cX
    cY
    cnmpt1plusg.k
    cnmpt2plusg.l
    cnmpt2plusg.a
    cnmpt2plusg.b
    wph
    @18
    @0
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    cnmpt1plusg.g
    @0
    cG
    cJ
    tgpcn.j
    @24
    tmdcn
    syl
    cnmpt22f
    eqeltrrd
end
