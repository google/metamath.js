include "cuni.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "elssuni.mm"
include "ssfi.mm"
include "ex.mm"
include "syl5.mm"
include "ssrdv.mm"

theorem unifi3
  let cA: class A
  let vx: setvar x


  assert |- ( U. A e. Fin -> A C_ Fin )

  proof
    cA
    cuni
    #
    cfn
    wcel
    #
    vx
    cA
    cfn
    vx
    cv
    #
    cA
    wcel
    @2
    @0
    wss
    #
    @1
    @2
    cfn
    wcel
    #
    @2
    cA
    elssuni
    @1
    @3
    @4
    @0
    @2
    ssfi
    ex
    syl5
    ssrdv
end
