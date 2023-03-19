include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cim.mm"
include "cr.mm"
include "sigarval.mm"
include "simpl.mm"
include "cjcld.mm"
include "simpr.mm"
include "mulcld.mm"
include "imcld.mm"
include "eqeltrd.mm"

theorem sigarim
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
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A G B ) e. RR )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cG
    co
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
    cr
    vx
    vy
    cA
    cB
    cG
    sigar
    sigarval
    @2
    @4
    @2
    @3
    cB
    @2
    cA
    @0
    @1
    simpl
    cjcld
    @0
    @1
    simpr
    mulcld
    imcld
    eqeltrd
end
