include "cc.mm"
include "cv.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "fvex.mm"
include "ovmpt2a.mm"

theorem sigarval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let cC: class C
  let vk: setvar k
  assume sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint k x
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A G B ) = ( Im ` ( ( * ` A ) x. B ) ) )

  proof
    vx
    vy
    cA
    cB
    cc
    cc
    vx
    cv
    #
    ccj
    cfv
    #
    vy
    cv
    #
    cmul
    co
    #
    cim
    cfv
    cA
    ccj
    cfv
    #
    cB
    cmul
    co
    #
    cim
    cfv
    cG
    @0
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    #
    @3
    @5
    cim
    @8
    @1
    @4
    @2
    cB
    cmul
    @8
    @0
    cA
    ccj
    @6
    @7
    simpl
    fveq2d
    @6
    @7
    simpr
    oveq12d
    fveq2d
    sigar
    @5
    cim
    fvex
    ovmpt2a
end
