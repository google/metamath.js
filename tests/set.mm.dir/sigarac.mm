include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cim.mm"
include "cneg.mm"
include "sigarval.mm"
include "cjcl.mm"
include "adantl.mm"
include "simpl.mm"
include "cjmuld.mm"
include "simpr.mm"
include "cjcjd.mm"
include "oveq1d.mm"
include "cjcld.mm"
include "mulcomd.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "mulcld.mm"
include "imcjd.mm"
include "3eqtrd.mm"
include "wceq.mm"
include "ancoms.mm"
include "negeqd.mm"
include "eqtr4d.mm"

theorem sigarac
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
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A G B ) = -u ( B G A ) )

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
    #
    cB
    ccj
    cfv
    #
    cA
    cmul
    co
    #
    cim
    cfv
    #
    cneg
    #
    cB
    cA
    cG
    co
    #
    cneg
    @2
    @3
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
    @5
    ccj
    cfv
    #
    cim
    cfv
    @7
    vx
    vy
    cA
    cB
    cG
    sigar
    sigarval
    @2
    @10
    @11
    cim
    @2
    @11
    @4
    ccj
    cfv
    #
    @9
    cmul
    co
    cB
    @9
    cmul
    co
    @10
    @2
    @4
    cA
    @1
    @4
    cc
    wcel
    @0
    cB
    cjcl
    adantl
    #
    @0
    @1
    simpl
    #
    cjmuld
    @2
    @12
    cB
    @9
    cmul
    @2
    cB
    @0
    @1
    simpr
    #
    cjcjd
    oveq1d
    @2
    cB
    @9
    @15
    @2
    cA
    @14
    cjcld
    mulcomd
    3eqtrrd
    fveq2d
    @2
    @5
    @2
    @4
    cA
    @13
    @14
    mulcld
    imcjd
    3eqtrd
    @2
    @8
    @6
    @1
    @0
    @8
    @6
    wceq
    vx
    vy
    cB
    cA
    cG
    sigar
    sigarval
    ancoms
    negeqd
    eqtr4d
end
