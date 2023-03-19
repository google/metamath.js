include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "csp.mm"
include "caddc.mm"
include "cbr.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-his2.mm"
include "3comr.mm"
include "wa.mm"
include "hvaddcl.mm"
include "braval.mm"
include "sylan2.mm"
include "3impb.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem braadd
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( bra ` A ) ` ( B +h C ) ) = ( ( ( bra ` A ) ` B ) + ( ( bra ` A ) ` C ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
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
    cva
    co
    #
    cA
    csp
    co
    #
    cB
    cA
    csp
    co
    #
    cC
    cA
    csp
    co
    #
    caddc
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
    @9
    cfv
    #
    cC
    @9
    cfv
    #
    caddc
    co
    @1
    @2
    @0
    @5
    @8
    wceq
    cB
    cC
    cA
    ax-his2
    3comr
    @0
    @1
    @2
    @10
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
    @13
    cB
    cC
    hvaddcl
    cA
    @4
    braval
    sylan2
    3impb
    @3
    @11
    @6
    @12
    @7
    caddc
    @0
    @1
    @11
    @6
    wceq
    @2
    cA
    cB
    braval
    3adant3
    @0
    @2
    @12
    @7
    wceq
    @1
    cA
    cC
    braval
    3adant2
    oveq12d
    3eqtr4d
end
