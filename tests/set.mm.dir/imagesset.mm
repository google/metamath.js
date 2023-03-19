include "csset.mm"
include "ccnv.mm"
include "cimage.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cima.mm"
include "wceq.mm"
include "wel.mm"
include "wrex.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "wbr.mm"
include "vex.mm"
include "elima.mm"
include "brcnv.mm"
include "brsset.mm"
include "bitri.mm"
include "rexbii.mm"
include "sylibr.mm"
include "ssriv.mm"
include "mpbiri.mm"
include "brimage.mm"
include "df-br.mm"
include "bitr3i.mm"
include "3imtr3i.mm"
include "gen2.mm"
include "wfun.mm"
include "wrel.mm"
include "wb.mm"
include "funimage.mm"
include "funrel.mm"
include "ssrel.mm"
include "mp2b.mm"
include "mpbir.mm"

theorem imagesset
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Image `' SSet C_ SSet

  proof
    csset
    ccnv
    #
    cimage
    #
    csset
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @1
    wcel
    #
    @5
    csset
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @8
    vx
    vy
    @4
    @0
    @3
    cima
    #
    wceq
    #
    @3
    @4
    wss
    #
    @6
    @7
    @11
    @12
    @3
    @10
    wss
    vy
    @3
    @10
    vy
    vx
    wel
    #
    @4
    vz
    cv
    #
    wss
    #
    vz
    @3
    wrex
    #
    @4
    @10
    wcel
    #
    @13
    @4
    @4
    wss
    #
    @16
    @4
    ssid
    @15
    @18
    vz
    @4
    @3
    @14
    @4
    @4
    sseq2
    rspcev
    mpan2
    @17
    @14
    @4
    @0
    wbr
    #
    vz
    @3
    wrex
    @16
    vz
    @4
    @0
    @3
    vy
    vex
    #
    elima
    @19
    @15
    vz
    @3
    @19
    @4
    @14
    csset
    wbr
    @15
    @14
    @4
    csset
    vz
    vex
    #
    @20
    brcnv
    @4
    @14
    @21
    brsset
    bitri
    rexbii
    bitri
    sylibr
    ssriv
    @4
    @10
    @3
    sseq2
    mpbiri
    @11
    @3
    @4
    @1
    wbr
    @6
    @3
    @4
    @0
    vx
    vex
    @20
    brimage
    @3
    @4
    @1
    df-br
    bitr3i
    @12
    @3
    @4
    csset
    wbr
    @7
    @3
    @4
    @20
    brsset
    @3
    @4
    csset
    df-br
    bitr3i
    3imtr3i
    gen2
    @1
    wfun
    @1
    wrel
    @2
    @9
    wb
    @0
    funimage
    @1
    funrel
    vx
    vy
    @1
    csset
    ssrel
    mp2b
    mpbir
end
