include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "wnel.mm"
include "cfn.mm"
include "snnex.mm"
include "wcel.mm"
include "wn.mm"
include "wss.mm"
include "snfi.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "exlimiv.mm"
include "abssi.mm"
include "ssexg.mm"
include "mpan.mm"
include "con3i.mm"
include "df-nel.mm"
include "3imtr4i.mm"
include "ax-mp.mm"

theorem fiprc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- Fin e/ _V

  proof
    vx
    cv
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    wex
    #
    vx
    cab
    #
    cvv
    wnel
    #
    cfn
    cvv
    wnel
    #
    vx
    vy
    snnex
    @5
    cvv
    wcel
    #
    wn
    cfn
    cvv
    wcel
    #
    wn
    @6
    @7
    @9
    @8
    @5
    cfn
    wss
    @9
    @8
    @4
    vx
    cfn
    @3
    @0
    cfn
    wcel
    #
    vy
    @3
    @10
    @2
    cfn
    wcel
    @1
    snfi
    @0
    @2
    cfn
    eleq1
    mpbiri
    exlimiv
    abssi
    @5
    cfn
    cvv
    ssexg
    mpan
    con3i
    @5
    cvv
    df-nel
    cfn
    cvv
    df-nel
    3imtr4i
    ax-mp
end
