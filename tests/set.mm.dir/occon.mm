include "chil.mm"
include "wss.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wi.mm"
include "ssralv.mm"
include "ralrimivw.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "adantl.mm"
include "ocval.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "3sstr4d.mm"
include "ex.mm"

theorem occon
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A C_ B -> ( _|_ ` B ) C_ ( _|_ ` A ) ) )

  proof
    cA
    chil
    wss
    #
    cB
    chil
    wss
    #
    wa
    #
    cA
    cB
    wss
    #
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wss
    @2
    @3
    wa
    vx
    cv
    vy
    cv
    csp
    co
    cc0
    wceq
    #
    vy
    cB
    wral
    #
    vx
    chil
    crab
    #
    @6
    vy
    cA
    wral
    #
    vx
    chil
    crab
    #
    @4
    @5
    @3
    @8
    @10
    wss
    #
    @2
    @3
    @7
    @9
    wi
    #
    vx
    chil
    wral
    @11
    @3
    @12
    vx
    chil
    @6
    vy
    cA
    cB
    ssralv
    ralrimivw
    @7
    @9
    vx
    chil
    ss2rab
    sylibr
    adantl
    @1
    @4
    @8
    wceq
    @0
    @3
    vx
    vy
    cB
    ocval
    ad2antlr
    @0
    @5
    @10
    wceq
    @1
    @3
    vx
    vy
    cA
    ocval
    ad2antrr
    3sstr4d
    ex
end
