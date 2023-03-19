include "cv.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "csn.mm"
include "wss.mm"
include "ctc.mm"
include "cfv.mm"
include "cun.mm"
include "snss.mm"
include "anbi1i.mm"
include "abbii.mm"
include "inteqi.mm"
include "tc2.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "tcvalg.mm"
include "ax-mp.mm"
include "3eqtr4ri.mm"

theorem tcsni
  let cA: class A
  let vx: setvar x
  assume tc2.1: |- A e. _V


  assert |- ( TC ` { A } ) = ( ( TC ` A ) u. { A } )

  proof
    cA
    vx
    cv
    #
    wcel
    #
    @0
    wtr
    #
    wa
    #
    vx
    cab
    #
    cint
    cA
    csn
    #
    @0
    wss
    #
    @2
    wa
    #
    vx
    cab
    #
    cint
    #
    cA
    ctc
    cfv
    @5
    cun
    @5
    ctc
    cfv
    #
    @4
    @8
    @3
    @7
    vx
    @1
    @6
    @2
    cA
    @0
    tc2.1
    snss
    anbi1i
    abbii
    inteqi
    vx
    cA
    tc2.1
    tc2
    @5
    cvv
    wcel
    @10
    @9
    wceq
    cA
    snex
    vx
    @5
    cvv
    tcvalg
    ax-mp
    3eqtr4ri
end
