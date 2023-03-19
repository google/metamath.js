include "cplusf.mm"
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
include "ctmd.mm"
include "eqid.mm"
include "tmdtopon.mm"
include "syl.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "plusfval.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "ctx.mm"
include "tmdcn.mm"
include "cnmpt12f.mm"
include "eqeltrrd.mm"

theorem cnmpt1plusg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume cnmpt1plusg.p: |- .+ = ( +g ` G )
  assume cnmpt1plusg.g: |- ( ph -> G e. TopMnd )
  assume cnmpt1plusg.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt1plusg.a: |- ( ph -> ( x e. X |-> A ) e. ( K Cn J ) )
  assume cnmpt1plusg.b: |- ( ph -> ( x e. X |-> B ) e. ( K Cn J ) )

  disjoint G x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint X x
  disjoint x y
  disjoint G y
  disjoint J y
  disjoint ph y
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X |-> ( A .+ B ) ) e. ( K Cn J ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cG
    cplusf
    cfv
    #
    co
    #
    cmpt
    vx
    cX
    cA
    cB
    c.pl
    co
    #
    cmpt
    cK
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
    cG
    cbs
    cfv
    #
    wcel
    #
    cB
    @4
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
    cK
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    @4
    ctopon
    cfv
    wcel
    #
    @7
    @3
    wcel
    @8
    cnmpt1plusg.k
    wph
    cG
    ctmd
    wcel
    #
    @10
    cnmpt1plusg.g
    cG
    cJ
    @4
    tgpcn.j
    @4
    eqid
    #
    tmdtopon
    syl
    #
    cnmpt1plusg.a
    @7
    cK
    cJ
    cX
    @4
    cnf2
    syl3anc
    vx
    cX
    @4
    cA
    @7
    @7
    eqid
    fmpt
    sylibr
    r19.21bi
    wph
    @6
    vx
    cX
    wph
    cX
    @4
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @6
    vx
    cX
    wral
    wph
    @9
    @10
    @14
    @3
    wcel
    @15
    cnmpt1plusg.k
    @13
    cnmpt1plusg.b
    @14
    cK
    cJ
    cX
    @4
    cnf2
    syl3anc
    vx
    cX
    @4
    cB
    @14
    @14
    eqid
    fmpt
    sylibr
    r19.21bi
    @4
    c.pl
    @0
    cG
    cA
    cB
    @12
    cnmpt1plusg.p
    @0
    eqid
    #
    plusfval
    syl2anc
    mpteq2dva
    wph
    vx
    cA
    cB
    @0
    cK
    cJ
    cJ
    cJ
    cX
    cnmpt1plusg.k
    cnmpt1plusg.a
    cnmpt1plusg.b
    wph
    @11
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
    @16
    tmdcn
    syl
    cnmpt12f
    eqeltrrd
end
