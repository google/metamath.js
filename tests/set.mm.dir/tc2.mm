include "ctc.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wss.mm"
include "cvv.mm"
include "wceq.mm"
include "tcvalg.mm"
include "ax-mp.mm"
include "trss.mm"
include "imdistanri.mm"
include "ss2abi.mm"
include "intss.mm"
include "eqsstri.mm"
include "wi.mm"
include "elintab.mm"
include "simpl.mm"
include "mpgbir.mm"
include "snss.mm"
include "mpbi.mm"
include "unssi.mm"
include "snid.mm"
include "elun2.mm"
include "cuni.mm"
include "uniun.mm"
include "tctr.mm"
include "df-tr.mm"
include "unisn.mm"
include "tcid.mm"
include "ssun1.mm"
include "sstri.mm"
include "mpbir.mm"
include "fvex.mm"
include "snex.mm"
include "unex.mm"
include "eleq2.mm"
include "treq.mm"
include "anbi12d.mm"
include "elab.mm"
include "mpbir2an.mm"
include "intss1.mm"
include "eqssi.mm"

theorem tc2
  let vx: setvar x
  let cA: class A
  assume tc2.1: |- A e. _V

  disjoint A x
  assert |- ( ( TC ` A ) u. { A } ) = |^| { x | ( A e. x /\ Tr x ) }

  proof
    cA
    ctc
    cfv
    #
    cA
    csn
    #
    cun
    #
    cA
    vx
    cv
    #
    wcel
    #
    @3
    wtr
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    @0
    @1
    @8
    @0
    cA
    @3
    wss
    #
    @5
    wa
    #
    vx
    cab
    #
    cint
    #
    @8
    cA
    cvv
    wcel
    #
    @0
    @12
    wceq
    tc2.1
    vx
    cA
    cvv
    tcvalg
    ax-mp
    @7
    @11
    wss
    @12
    @8
    wss
    @6
    @10
    vx
    @5
    @4
    @9
    @3
    cA
    trss
    imdistanri
    ss2abi
    @7
    @11
    intss
    ax-mp
    eqsstri
    cA
    @8
    wcel
    #
    @1
    @8
    wss
    @14
    @6
    @4
    wi
    vx
    @6
    vx
    cA
    tc2.1
    elintab
    @4
    @5
    simpl
    mpgbir
    cA
    @8
    tc2.1
    snss
    mpbi
    unssi
    @2
    @7
    wcel
    #
    @8
    @2
    wss
    @15
    cA
    @2
    wcel
    #
    @2
    wtr
    #
    cA
    @1
    wcel
    @16
    cA
    tc2.1
    snid
    cA
    @1
    @0
    elun2
    ax-mp
    @17
    @2
    cuni
    #
    @2
    wss
    @18
    @0
    @2
    @18
    @0
    cuni
    #
    @1
    cuni
    #
    cun
    @0
    @0
    @1
    uniun
    @19
    @20
    @0
    @0
    wtr
    @19
    @0
    wss
    cA
    tctr
    @0
    df-tr
    mpbi
    @20
    cA
    @0
    cA
    tc2.1
    unisn
    @13
    cA
    @0
    wss
    tc2.1
    cA
    cvv
    tcid
    ax-mp
    eqsstri
    unssi
    eqsstri
    @0
    @1
    ssun1
    sstri
    @2
    df-tr
    mpbir
    @6
    @16
    @17
    wa
    vx
    @2
    @0
    @1
    cA
    ctc
    fvex
    cA
    snex
    unex
    @3
    @2
    wceq
    @4
    @16
    @5
    @17
    @3
    @2
    cA
    eleq2
    @3
    @2
    treq
    anbi12d
    elab
    mpbir2an
    @2
    @7
    intss1
    ax-mp
    eqssi
end
