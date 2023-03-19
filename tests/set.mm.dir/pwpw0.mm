include "cv.mm"
include "c0.mm"
include "csn.mm"
include "wss.mm"
include "cab.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "cpr.mm"
include "wn.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "dfss2.mm"
include "velsn.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitri.mm"
include "wex.mm"
include "neq0.mm"
include "exintr.mm"
include "syl5bi.mm"
include "exancom.mm"
include "df-clel.mm"
include "bitr4i.mm"
include "snssi.mm"
include "sylbi.mm"
include "syl6.mm"
include "anc2li.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "orrd.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "eqimss.mm"
include "jaoi.mm"
include "impbii.mm"
include "abbii.mm"
include "df-pw.mm"
include "dfpr2.mm"
include "3eqtr4i.mm"

theorem pwpw0
  let vx: setvar x
  let vy: setvar y


  assert |- ~P { (/) } = { (/) , { (/) } }

  proof
    vx
    cv
    #
    c0
    csn
    #
    wss
    #
    vx
    cab
    @0
    c0
    wceq
    #
    @0
    @1
    wceq
    #
    wo
    #
    vx
    cab
    @1
    cpw
    c0
    @1
    cpr
    @2
    @5
    vx
    @2
    @5
    @2
    @3
    @4
    @2
    @3
    wn
    #
    @2
    @1
    @0
    wss
    #
    wa
    @4
    @2
    @6
    @7
    @2
    vy
    cv
    #
    @0
    wcel
    #
    @8
    c0
    wceq
    #
    wi
    #
    vy
    wal
    #
    @6
    @7
    wi
    @2
    @9
    @8
    @1
    wcel
    #
    wi
    #
    vy
    wal
    @12
    vy
    @0
    @1
    dfss2
    @14
    @11
    vy
    @13
    @10
    @9
    vy
    c0
    velsn
    imbi2i
    albii
    bitri
    @12
    @6
    @9
    @10
    wa
    vy
    wex
    #
    @7
    @6
    @9
    vy
    wex
    @12
    @15
    vy
    @0
    neq0
    @9
    @10
    vy
    exintr
    syl5bi
    @15
    c0
    @0
    wcel
    #
    @7
    @15
    @10
    @9
    wa
    vy
    wex
    @16
    @9
    @10
    vy
    exancom
    vy
    c0
    @0
    df-clel
    bitr4i
    c0
    @0
    snssi
    sylbi
    syl6
    sylbi
    anc2li
    @0
    @1
    eqss
    syl6ibr
    orrd
    @3
    @2
    @4
    @3
    @2
    c0
    @1
    wss
    @1
    0ss
    @0
    c0
    @1
    sseq1
    mpbiri
    @0
    @1
    eqimss
    jaoi
    impbii
    abbii
    vx
    @1
    df-pw
    vx
    c0
    @1
    dfpr2
    3eqtr4i
end
