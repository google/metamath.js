include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "crest.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "elrest.mm"
include "sylan.mm"
include "wex.mm"
include "wss.mm"
include "selpw.mm"
include "anbi1i.mm"
include "exbii.mm"
include "sstr2.mm"
include "com12.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "impel.mm"
include "inss2.mm"
include "adantl.mm"
include "ssind.mm"
include "exlimiv.mm"
include "mpi.mm"
include "ssid.mm"
include "a1i.mm"
include "id.mm"
include "eqssd.mm"
include "vex.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "impbii.mm"
include "bitri.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "syl6bb.mm"
include "eqrdv.mm"

theorem bj-restpw
  let cA: class A
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Y e. V /\ A e. W ) -> ( ~P Y |`t A ) = ~P ( Y i^i A ) )

  proof
    cY
    cV
    wcel
    #
    cA
    cW
    wcel
    #
    wa
    #
    vx
    cY
    cpw
    #
    cA
    crest
    co
    #
    cY
    cA
    cin
    #
    cpw
    #
    @2
    vx
    cv
    #
    @4
    wcel
    #
    @7
    vy
    cv
    #
    cA
    cin
    #
    wceq
    #
    vy
    @3
    wrex
    #
    @7
    @6
    wcel
    #
    @0
    @3
    cvv
    wcel
    @1
    @8
    @12
    wb
    cY
    cV
    pwexg
    vy
    @7
    cA
    @3
    cvv
    cW
    elrest
    sylan
    @9
    @3
    wcel
    #
    @11
    wa
    #
    vy
    wex
    #
    @7
    @5
    wss
    #
    @12
    @13
    @16
    @9
    cY
    wss
    #
    @11
    wa
    #
    vy
    wex
    #
    @17
    @15
    @19
    vy
    @14
    @18
    @11
    vy
    cY
    selpw
    anbi1i
    exbii
    @20
    @17
    @19
    @17
    vy
    @19
    @7
    cY
    cA
    @18
    @7
    @9
    wss
    #
    @7
    cY
    wss
    #
    @11
    @21
    @18
    @22
    @7
    @9
    cY
    sstr2
    com12
    @11
    @21
    @10
    @9
    wss
    @9
    cA
    inss1
    @7
    @10
    @9
    sseq1
    mpbiri
    impel
    @11
    @7
    cA
    wss
    #
    @18
    @11
    @23
    @10
    cA
    wss
    @9
    cA
    inss2
    @7
    @10
    cA
    sseq1
    mpbiri
    adantl
    ssind
    exlimiv
    @17
    @22
    @23
    @20
    @17
    @5
    cY
    wss
    @22
    cY
    cA
    inss1
    @7
    @5
    cY
    sstr2
    mpi
    @17
    @5
    cA
    wss
    @23
    cY
    cA
    inss2
    @7
    @5
    cA
    sstr2
    mpi
    @23
    @22
    @7
    @7
    cA
    cin
    #
    wceq
    #
    @20
    @23
    @7
    @24
    @23
    @7
    @7
    cA
    @7
    @7
    wss
    @23
    @7
    ssid
    a1i
    @23
    id
    ssind
    @24
    @7
    wss
    @23
    @7
    cA
    inss1
    a1i
    eqssd
    @19
    @22
    @25
    wa
    vy
    @7
    vx
    vex
    @9
    @7
    wceq
    #
    @18
    @22
    @11
    @25
    @9
    @7
    cY
    sseq1
    @26
    @10
    @24
    @7
    @9
    @7
    cA
    ineq1
    eqeq2d
    anbi12d
    spcev
    sylan2
    syl2anc
    impbii
    bitri
    @11
    vy
    @3
    df-rex
    vx
    @5
    selpw
    3bitr4i
    syl6bb
    eqrdv
end
