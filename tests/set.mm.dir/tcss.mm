include "wss.mm"
include "ctc.mm"
include "cfv.mm"
include "cv.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ssex.mm"
include "tcvalg.mm"
include "syl.mm"
include "sstr2.mm"
include "anim1d.mm"
include "ss2abdv.mm"
include "intss.mm"
include "ax-mp.mm"
include "syl6sseqr.mm"
include "eqsstrd.mm"

theorem tcss
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume tc2.1: |- A e. _V


  assert |- ( B C_ A -> ( TC ` B ) C_ ( TC ` A ) )

  proof
    cB
    cA
    wss
    #
    cB
    ctc
    cfv
    #
    cB
    vx
    cv
    #
    wss
    #
    @2
    wtr
    #
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
    #
    @0
    cB
    cvv
    wcel
    @1
    @7
    wceq
    cB
    cA
    tc2.1
    ssex
    vx
    cB
    cvv
    tcvalg
    syl
    @0
    @7
    cA
    @2
    wss
    #
    @4
    wa
    #
    vx
    cab
    #
    cint
    #
    @8
    @0
    @11
    @6
    wss
    @7
    @12
    wss
    @0
    @10
    @5
    vx
    @0
    @9
    @3
    @4
    cB
    cA
    @2
    sstr2
    anim1d
    ss2abdv
    @11
    @6
    intss
    syl
    cA
    cvv
    wcel
    @8
    @12
    wceq
    tc2.1
    vx
    cA
    cvv
    tcvalg
    ax-mp
    syl6sseqr
    eqsstrd
end
