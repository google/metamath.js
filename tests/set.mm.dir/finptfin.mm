include "cfn.mm"
include "wcel.mm"
include "cptfin.mm"
include "wel.mm"
include "crab.mm"
include "cuni.mm"
include "wral.mm"
include "rabfi.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "isptfin.mm"
include "mpbird.mm"

theorem finptfin
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. Fin -> A e. PtFin )

  proof
    cA
    cfn
    wcel
    #
    cA
    cptfin
    wcel
    vx
    vy
    wel
    #
    vy
    cA
    crab
    cfn
    wcel
    #
    vx
    cA
    cuni
    #
    wral
    @0
    @2
    vx
    @3
    @1
    vy
    cA
    rabfi
    ralrimivw
    vx
    vy
    cA
    cfn
    @3
    @3
    eqid
    isptfin
    mpbird
end
