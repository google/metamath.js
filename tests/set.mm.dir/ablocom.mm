include "cablo.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cgr.mm"
include "isablo.mm"
include "simprbi.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem ablocom
  let cA: class A
  let cB: class B
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume ablcom.1: |- X = ran G


  assert |- ( ( G e. AbelOp /\ A e. X /\ B e. X ) -> ( A G B ) = ( B G A ) )

  proof
    cG
    cablo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cG
    co
    #
    cB
    cA
    cG
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    @7
    @6
    cG
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @5
    @0
    cG
    cgr
    wcel
    @11
    vx
    vy
    cG
    cX
    ablcom.1
    isablo
    simprbi
    @10
    @5
    cA
    @7
    cG
    co
    #
    @7
    cA
    cG
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cX
    cX
    @6
    cA
    wceq
    @8
    @12
    @9
    @13
    @6
    cA
    @7
    cG
    oveq1
    @6
    cA
    @7
    cG
    oveq2
    eqeq12d
    @7
    cB
    wceq
    @12
    @3
    @13
    @4
    @7
    cB
    cA
    cG
    oveq2
    @7
    cB
    cA
    cG
    oveq1
    eqeq12d
    rspc2v
    syl5com
    3impib
end
