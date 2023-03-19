include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cmul.mm"
include "ccn.mm"
include "wceq.mm"
include "divrec.mm"
include "3expb.mm"
include "ancoms.mm"
include "mpteq2dva.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "cnmptid.mm"
include "reccl.mm"
include "cnmptc.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "eqeltrd.mm"

theorem divccn
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  assume expcn.j: |- J = ( TopOpen ` CCfld )

  disjoint A x
  disjoint J x
  disjoint k n
  disjoint k x
  disjoint J k
  disjoint n x
  disjoint J n
  disjoint N n
  disjoint N x
  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( x e. CC |-> ( x / A ) ) e. ( J Cn J ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    vx
    cc
    vx
    cv
    #
    cA
    cdiv
    co
    #
    cmpt
    vx
    cc
    @3
    c1
    cA
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    cJ
    cJ
    ccn
    co
    @2
    vx
    cc
    @4
    @6
    @3
    cc
    wcel
    #
    @2
    @4
    @6
    wceq
    #
    @7
    @0
    @1
    @8
    @3
    cA
    divrec
    3expb
    ancoms
    mpteq2dva
    @2
    vx
    @3
    @5
    cmul
    cJ
    cJ
    cJ
    cJ
    cc
    cJ
    cc
    ctopon
    cfv
    wcel
    @2
    cJ
    expcn.j
    cnfldtopon
    a1i
    #
    @2
    vx
    cJ
    cc
    @9
    cnmptid
    @2
    vx
    @5
    cJ
    cJ
    cc
    cc
    @9
    @9
    cA
    reccl
    cnmptc
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    @2
    cJ
    expcn.j
    mulcn
    a1i
    cnmpt12f
    eqeltrd
end
