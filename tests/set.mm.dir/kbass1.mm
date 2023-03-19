include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "ck.mm"
include "co.mm"
include "cfv.mm"
include "csp.mm"
include "csm.mm"
include "cbr.mm"
include "kbval.mm"
include "wceq.mm"
include "braval.mm"
include "3adant1.mm"
include "oveq1d.mm"
include "eqtr4d.mm"

theorem kbass1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A ketbra B ) ` C ) = ( ( ( bra ` B ) ` C ) .h A ) )

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
    cC
    cA
    cB
    ck
    co
    cfv
    cC
    cB
    csp
    co
    #
    cA
    csm
    co
    cC
    cB
    cbr
    cfv
    cfv
    #
    cA
    csm
    co
    cA
    cB
    cC
    kbval
    @3
    @5
    @4
    cA
    csm
    @1
    @2
    @5
    @4
    wceq
    @0
    cB
    cC
    braval
    3adant1
    oveq1d
    eqtr4d
end
