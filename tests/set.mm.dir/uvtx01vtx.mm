include "c0.mm"
include "wceq.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "wrex.mm"
include "chash.mm"
include "c1.mm"
include "uvtxval.mm"
include "a1i.mm"
include "neeq1d.mm"
include "wb.mm"
include "rabn0.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wn.mm"
include "wal.mm"
include "falseral0.mm"
include "ex.mm"
include "noel.mm"
include "mpg.mm"
include "wss.mm"
include "ssdif0.mm"
include "wo.mm"
include "sssn.mm"
include "ne0i.mm"
include "eqneqall.mm"
include "syl5.mm"
include "ax-1.mm"
include "jaoi.mm"
include "sylbi.mm"
include "sylbir.mm"
include "syl.mm"
include "impcom.mm"
include "vsnid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "ralel.mm"
include "difeq1.mm"
include "difid.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "jca.mm"
include "impbii.mm"
include "exbidv.mm"
include "cedg.mm"
include "eqeq1i.mm"
include "nbgr0edg.mm"
include "eleq2d.mm"
include "rexralbidv.mm"
include "df-rex.mm"
include "syl6bb.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvexi.mm"
include "hash1snb.mm"
include "mp1i.mm"
include "3bitr4d.mm"
include "3bitrd.mm"

theorem uvtx01vtx
  let cE: class E
  let cG: class G
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  let cN: class N
  let ve: setvar e
  let vk: setvar k
  let cW: class W
  assume uvtxel.v: |- V = ( Vtx ` G )
  assume isuvtx.e: |- E = ( Edg ` G )


  assert |- ( E = (/) -> ( ( UnivVtx ` G ) =/= (/) <-> ( # ` V ) = 1 ) )

  proof
    cE
    c0
    wceq
    #
    cG
    cuvtx
    cfv
    #
    c0
    wne
    vn
    cv
    #
    cG
    vv
    cv
    #
    cnbgr
    co
    #
    wcel
    #
    vn
    cV
    @3
    csn
    #
    cdif
    #
    wral
    #
    vv
    cV
    crab
    #
    c0
    wne
    #
    @8
    vv
    cV
    wrex
    #
    cV
    chash
    cfv
    c1
    wceq
    #
    @0
    @1
    @9
    c0
    @1
    @9
    wceq
    @0
    vv
    vn
    cG
    cV
    uvtxel.v
    uvtxval
    a1i
    neeq1d
    @10
    @11
    wb
    @0
    @8
    vv
    cV
    rabn0
    a1i
    @0
    @3
    cV
    wcel
    #
    @2
    c0
    wcel
    #
    vn
    @7
    wral
    #
    wa
    #
    vv
    wex
    #
    cV
    @6
    wceq
    #
    vv
    wex
    #
    @11
    @12
    @0
    @16
    @18
    vv
    @16
    @18
    wb
    @0
    @16
    @18
    @15
    @13
    @18
    @15
    @7
    c0
    wceq
    #
    @13
    @18
    wi
    #
    @14
    wn
    #
    @15
    @20
    wi
    vn
    @22
    vn
    wal
    @15
    @20
    @14
    vn
    @7
    falseral0
    ex
    @2
    noel
    mpg
    @20
    cV
    @6
    wss
    #
    @21
    cV
    @6
    ssdif0
    @23
    cV
    c0
    wceq
    #
    @18
    wo
    @21
    cV
    @3
    sssn
    @24
    @21
    @18
    @13
    cV
    c0
    wne
    @24
    @18
    cV
    @3
    ne0i
    @18
    cV
    c0
    eqneqall
    syl5
    @18
    @13
    ax-1
    jaoi
    sylbi
    sylbir
    syl
    impcom
    @18
    @13
    @15
    @18
    @13
    @3
    @6
    wcel
    vv
    vsnid
    cV
    @6
    @3
    eleq2
    mpbiri
    @18
    @15
    @14
    vn
    c0
    wral
    vn
    c0
    ralel
    @18
    @14
    vn
    @7
    c0
    @18
    @7
    @6
    @6
    cdif
    c0
    cV
    @6
    @6
    difeq1
    @6
    difid
    syl6eq
    raleqdv
    mpbiri
    jca
    impbii
    a1i
    exbidv
    @0
    @11
    @15
    vv
    cV
    wrex
    @17
    @0
    @5
    @14
    vv
    vn
    cV
    @7
    @0
    @4
    c0
    @2
    @0
    cG
    cedg
    cfv
    #
    c0
    wceq
    @4
    c0
    wceq
    cE
    @25
    c0
    isuvtx.e
    eqeq1i
    cG
    @3
    nbgr0edg
    sylbi
    eleq2d
    rexralbidv
    @15
    vv
    cV
    df-rex
    syl6bb
    cV
    cvv
    wcel
    @12
    @19
    wb
    @0
    cV
    cG
    cvtx
    uvtxel.v
    fvexi
    cV
    cvv
    vv
    hash1snb
    mp1i
    3bitr4d
    3bitrd
end
