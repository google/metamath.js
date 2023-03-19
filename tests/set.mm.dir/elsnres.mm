include "csn.mm"
include "cres.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "elres.mm"
include "rexcom4.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rexsn.mm"
include "exbii.mm"
include "3bitri.mm"

theorem elsnres
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume elsnres.1: |- C e. _V

  disjoint A y
  disjoint B y
  disjoint C y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A e. ( B |` { C } ) <-> E. y ( A = <. C , y >. /\ <. C , y >. e. B ) )

  proof
    cA
    cB
    cC
    csn
    #
    cres
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @3
    cB
    wcel
    #
    wa
    #
    vy
    wex
    vx
    @0
    wrex
    @6
    vx
    @0
    wrex
    #
    vy
    wex
    cA
    cC
    @2
    cop
    #
    wceq
    #
    @8
    cB
    wcel
    #
    wa
    #
    vy
    wex
    vx
    vy
    cA
    cB
    @0
    elres
    @6
    vx
    vy
    @0
    rexcom4
    @7
    @11
    vy
    @6
    @11
    vx
    cC
    elsnres.1
    @1
    cC
    wceq
    #
    @4
    @9
    @5
    @10
    @12
    @3
    @8
    cA
    @1
    cC
    @2
    opeq1
    #
    eqeq2d
    @12
    @3
    @8
    cB
    @13
    eleq1d
    anbi12d
    rexsn
    exbii
    3bitri
end
