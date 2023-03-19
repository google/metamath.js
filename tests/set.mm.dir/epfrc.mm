include "cep.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "cin.mm"
include "frc.mm"
include "wcel.mm"
include "dfin5.mm"
include "epel.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "sylibr.mm"

theorem epfrc
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume epfrc.1: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( _E Fr A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) )

  proof
    cA
    cep
    wfr
    cB
    cA
    wss
    cB
    c0
    wne
    w3a
    vy
    cv
    #
    vx
    cv
    #
    cep
    wbr
    #
    vy
    cB
    crab
    #
    c0
    wceq
    #
    vx
    cB
    wrex
    cB
    @1
    cin
    #
    c0
    wceq
    #
    vx
    cB
    wrex
    vx
    vy
    cA
    cB
    cep
    epfrc.1
    frc
    @6
    @4
    vx
    cB
    @5
    @3
    c0
    @5
    @0
    @1
    wcel
    #
    vy
    cB
    crab
    @3
    vy
    cB
    @1
    dfin5
    @2
    @7
    vy
    cB
    vy
    vx
    epel
    rabbii
    eqtr4i
    eqeq1i
    rexbii
    sylibr
end
