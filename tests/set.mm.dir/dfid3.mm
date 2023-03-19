include "cid.mm"
include "weq.mm"
include "copab.mm"
include "df-id.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wal.mm"
include "wb.mm"
include "ancom.mm"
include "equcom.mm"
include "anbi1i.mm"
include "bitri.mm"
include "exbii.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "equsexvw.mm"
include "equid.mm"
include "biantru.mm"
include "3bitri.mm"
include "nfe1.mm"
include "19.9.mm"
include "bitr4i.mm"
include "equequ2.mm"
include "anbi12d.mm"
include "sps.mm"
include "drex1.mm"
include "drex2.mm"
include "syl5bb.mm"
include "wn.mm"
include "nfnae.mm"
include "nfcvd.mm"
include "nfcvf2.mm"
include "nfopd.mm"
include "nfeqd.mm"
include "nfand.mm"
include "wi.mm"
include "a1i.mm"
include "cbvexd.mm"
include "exbid.mm"
include "pm2.61i.mm"
include "abbii.mm"
include "df-opab.mm"
include "3eqtr4i.mm"
include "eqtri.mm"

theorem dfid3
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z


  assert |- _I = { <. x , y >. | x = y }

  proof
    cid
    vx
    vz
    weq
    #
    vx
    vz
    copab
    #
    vx
    vy
    weq
    #
    vx
    vy
    copab
    #
    vx
    vz
    df-id
    vw
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    @0
    wa
    #
    vz
    wex
    #
    vx
    wex
    #
    vw
    cab
    @4
    @5
    vy
    cv
    #
    cop
    #
    wceq
    #
    @2
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vw
    cab
    @1
    @3
    @11
    @17
    vw
    @2
    vx
    wal
    #
    @11
    @17
    wb
    @11
    @4
    @5
    @5
    cop
    #
    wceq
    #
    vx
    vx
    weq
    #
    wa
    #
    vx
    wex
    #
    vx
    wex
    #
    @18
    @17
    @11
    @23
    @24
    @10
    @22
    vx
    @10
    vz
    vx
    weq
    #
    @8
    wa
    #
    vz
    wex
    @20
    @22
    @9
    @26
    vz
    @9
    @0
    @8
    wa
    @26
    @8
    @0
    ancom
    @0
    @25
    @8
    vx
    vz
    equcom
    anbi1i
    bitri
    exbii
    @8
    @20
    vz
    vx
    @25
    @7
    @19
    @4
    @6
    @5
    @5
    opeq2
    eqeq2d
    equsexvw
    @21
    @20
    vx
    equid
    biantru
    3bitri
    exbii
    @23
    vx
    @22
    vx
    nfe1
    19.9
    bitr4i
    @23
    @16
    vx
    vy
    vx
    @22
    @15
    vx
    vy
    @2
    @22
    @15
    wb
    vx
    @2
    @20
    @14
    @21
    @2
    @2
    @19
    @13
    @4
    @5
    @12
    @5
    opeq2
    eqeq2d
    vx
    vy
    vx
    equequ2
    anbi12d
    sps
    drex1
    drex2
    syl5bb
    @18
    wn
    #
    @10
    @16
    vx
    vx
    vy
    vx
    nfnae
    @27
    @9
    @15
    vz
    vy
    vx
    vy
    vy
    nfnae
    @27
    @8
    @0
    vy
    @27
    vy
    @4
    @7
    @27
    vy
    @4
    nfcvd
    @27
    vy
    @5
    @6
    vx
    vy
    nfcvf2
    #
    @27
    vy
    @6
    nfcvd
    #
    nfopd
    nfeqd
    @27
    vy
    @5
    @6
    @28
    @29
    nfeqd
    nfand
    vz
    vy
    weq
    #
    @9
    @15
    wb
    wi
    @27
    @30
    @8
    @14
    @0
    @2
    @30
    @7
    @13
    @4
    @6
    @12
    @5
    opeq2
    eqeq2d
    vz
    vy
    vx
    equequ2
    anbi12d
    a1i
    cbvexd
    exbid
    pm2.61i
    abbii
    @0
    vx
    vz
    vw
    df-opab
    @2
    vx
    vy
    vw
    df-opab
    3eqtr4i
    eqtri
end
