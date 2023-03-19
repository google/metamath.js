include "chil.mm"
include "wcel.mm"
include "cbr.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cmpt.mm"
include "brafval.mm"
include "fveq1d.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem braval
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( bra ` A ) ` B ) = ( B .ih A ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    cB
    cA
    cbr
    cfv
    #
    cfv
    cB
    vx
    chil
    vx
    cv
    #
    cA
    csp
    co
    #
    cmpt
    #
    cfv
    cB
    cA
    csp
    co
    #
    @0
    cB
    @1
    @4
    vx
    cA
    brafval
    fveq1d
    vx
    cB
    @3
    @5
    chil
    @4
    @2
    cB
    cA
    csp
    oveq1
    @4
    eqid
    cB
    cA
    csp
    ovex
    fvmpt
    sylan9eq
end
