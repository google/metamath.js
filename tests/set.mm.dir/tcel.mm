include "wcel.mm"
include "ctc.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "tcvalg.mm"
include "wi.mm"
include "ssel.mm"
include "trss.mm"
include "com12.mm"
include "syl6com.mm"
include "impd.mm"
include "simpr.mm"
include "a1i.mm"
include "jcad.mm"
include "ss2abdv.mm"
include "intss.mm"
include "syl.mm"
include "cvv.mm"
include "wceq.mm"
include "ax-mp.mm"
include "syl6sseqr.mm"
include "eqsstrd.mm"

theorem tcel
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume tc2.1: |- A e. _V


  assert |- ( B e. A -> ( TC ` B ) C_ ( TC ` A ) )

  proof
    cB
    cA
    wcel
    #
    cB
    ctc
    cfv
    cB
    vx
    cv
    #
    wss
    #
    @1
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
    vx
    cB
    cA
    tcvalg
    @0
    @6
    cA
    @1
    wss
    #
    @3
    wa
    #
    vx
    cab
    #
    cint
    #
    @7
    @0
    @10
    @5
    wss
    @6
    @11
    wss
    @0
    @9
    @4
    vx
    @0
    @9
    @2
    @3
    @0
    @8
    @3
    @2
    @8
    @0
    cB
    @1
    wcel
    #
    @3
    @2
    wi
    cA
    @1
    cB
    ssel
    @3
    @12
    @2
    @1
    cB
    trss
    com12
    syl6com
    impd
    @9
    @3
    wi
    @0
    @8
    @3
    simpr
    a1i
    jcad
    ss2abdv
    @10
    @5
    intss
    syl
    cA
    cvv
    wcel
    @7
    @11
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
