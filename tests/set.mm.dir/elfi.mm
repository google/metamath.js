include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cab.mm"
include "fival.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elabg.mm"
include "sylan9bbr.mm"

theorem elfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint V x
  disjoint W x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  assert |- ( ( A e. V /\ B e. W ) -> ( A e. ( fi ` B ) <-> E. x e. ( ~P B i^i Fin ) A = |^| x ) )

  proof
    cB
    cW
    wcel
    #
    cA
    cB
    cfi
    cfv
    #
    wcel
    cA
    vy
    cv
    #
    vx
    cv
    cint
    #
    wceq
    #
    vx
    cB
    cpw
    cfn
    cin
    #
    wrex
    #
    vy
    cab
    #
    wcel
    cA
    cV
    wcel
    cA
    @3
    wceq
    #
    vx
    @5
    wrex
    #
    @0
    @1
    @7
    cA
    vx
    vy
    cB
    cW
    fival
    eleq2d
    @6
    @9
    vy
    cA
    cV
    @2
    cA
    wceq
    @4
    @8
    vx
    @5
    @2
    cA
    @3
    eqeq1
    rexbidv
    elabg
    sylan9bbr
end
