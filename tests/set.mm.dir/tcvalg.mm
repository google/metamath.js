include "cv.mm"
include "ctc.mm"
include "cfv.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "abbidv.mm"
include "inteqd.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "tz9.1c.mm"
include "df-tc.mm"
include "fvmpt2.mm"
include "mp2an.mm"
include "vtoclg.mm"

theorem tcvalg
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. V -> ( TC ` A ) = |^| { x | ( A C_ x /\ Tr x ) } )

  proof
    vy
    cv
    #
    ctc
    cfv
    #
    @0
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
    wceq
    #
    cA
    ctc
    cfv
    #
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
    wceq
    vy
    cA
    cV
    @0
    cA
    wceq
    #
    @1
    @9
    @7
    @13
    @0
    cA
    ctc
    fveq2
    @14
    @6
    @12
    @14
    @5
    @11
    vx
    @14
    @3
    @10
    @4
    @0
    cA
    @2
    sseq1
    anbi1d
    abbidv
    inteqd
    eqeq12d
    @0
    cvv
    wcel
    @7
    cvv
    wcel
    @8
    vy
    vex
    #
    vx
    @0
    @15
    tz9.1c
    vy
    cvv
    @7
    cvv
    ctc
    vy
    vx
    df-tc
    fvmpt2
    mp2an
    vtoclg
end
