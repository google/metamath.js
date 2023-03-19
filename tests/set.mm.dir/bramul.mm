include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "csp.mm"
include "cmul.mm"
include "cbr.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-his3.mm"
include "3comr.mm"
include "wa.mm"
include "hvmulcl.mm"
include "braval.mm"
include "sylan2.mm"
include "3impb.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem bramul
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ B e. CC /\ C e. ~H ) -> ( ( bra ` A ) ` ( B .h C ) ) = ( B x. ( ( bra ` A ) ` C ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    cB
    cC
    csm
    co
    #
    cA
    csp
    co
    #
    cB
    cC
    cA
    csp
    co
    #
    cmul
    co
    #
    @4
    cA
    cbr
    cfv
    #
    cfv
    #
    cB
    cC
    @8
    cfv
    #
    cmul
    co
    @1
    @2
    @0
    @5
    @7
    wceq
    cB
    cC
    cA
    ax-his3
    3comr
    @0
    @1
    @2
    @9
    @5
    wceq
    #
    @1
    @2
    wa
    @0
    @4
    chil
    wcel
    @11
    cB
    cC
    hvmulcl
    cA
    @4
    braval
    sylan2
    3impb
    @3
    @10
    @6
    cB
    cmul
    @0
    @2
    @10
    @6
    wceq
    @1
    cA
    cC
    braval
    3adant2
    oveq2d
    3eqtr4d
end
