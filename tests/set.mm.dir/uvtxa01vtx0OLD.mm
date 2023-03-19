include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "wrex.mm"
include "chash.mm"
include "c1.mm"
include "uvtxavalOLD.mm"
include "adantr.mm"
include "neeq1d.mm"
include "wb.mm"
include "rabn0.mm"
include "a1i.mm"
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
include "ral0.mm"
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
include "ralbidv.mm"
include "rexbidv.mm"
include "adantl.mm"
include "df-rex.mm"
include "syl6bb.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hash1snb.mm"
include "mp1i.mm"
include "3bitr4d.mm"
include "3bitrd.mm"

theorem uvtxa01vtx0OLD
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let vn: setvar n
  let vv: setvar v
  let cN: class N
  let ve: setvar e
  let vk: setvar k
  assume uvtxel.v: |- V = ( Vtx ` G )
  assume isuvtx.e: |- E = ( Edg ` G )


  assert |- ( ( G e. W /\ E = (/) ) -> ( ( UnivVtx ` G ) =/= (/) <-> ( # ` V ) = 1 ) )

  proof
    cG
    cW
    wcel
    #
    cE
    c0
    wceq
    #
    wa
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
    @5
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
    @10
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
    @2
    @3
    @11
    c0
    @0
    @3
    @11
    wceq
    @1
    vv
    vn
    cG
    cV
    cW
    uvtxel.v
    uvtxavalOLD
    adantr
    neeq1d
    @12
    @13
    wb
    @2
    @10
    vv
    cV
    rabn0
    a1i
    @2
    @5
    cV
    wcel
    #
    @4
    c0
    wcel
    #
    vn
    @9
    wral
    #
    wa
    #
    vv
    wex
    #
    cV
    @8
    wceq
    #
    vv
    wex
    #
    @13
    @14
    @2
    @18
    @20
    vv
    @18
    @20
    wb
    @2
    @18
    @20
    @17
    @15
    @20
    @17
    @9
    c0
    wceq
    #
    @15
    @20
    wi
    #
    @16
    wn
    #
    @17
    @22
    wi
    vn
    @24
    vn
    wal
    @17
    @22
    @16
    vn
    @9
    falseral0
    ex
    @4
    noel
    mpg
    @22
    cV
    @8
    wss
    #
    @23
    cV
    @8
    ssdif0
    @25
    cV
    c0
    wceq
    #
    @20
    wo
    @23
    cV
    @5
    sssn
    @26
    @23
    @20
    @15
    cV
    c0
    wne
    @26
    @20
    cV
    @5
    ne0i
    @20
    cV
    c0
    eqneqall
    syl5
    @20
    @15
    ax-1
    jaoi
    sylbi
    sylbir
    syl
    impcom
    @20
    @15
    @17
    @20
    @15
    @5
    @8
    wcel
    vv
    vsnid
    cV
    @8
    @5
    eleq2
    mpbiri
    @20
    @17
    @16
    vn
    c0
    wral
    @16
    vn
    ral0
    @20
    @16
    vn
    @9
    c0
    @20
    @9
    @8
    @8
    cdif
    c0
    cV
    @8
    @8
    difeq1
    @8
    difid
    syl6eq
    raleqdv
    mpbiri
    jca
    impbii
    a1i
    exbidv
    @2
    @13
    @17
    vv
    cV
    wrex
    #
    @19
    @1
    @13
    @27
    wb
    @0
    @1
    @10
    @17
    vv
    cV
    @1
    @7
    @16
    vn
    @9
    @1
    @6
    c0
    @4
    @1
    cG
    cedg
    cfv
    #
    c0
    wceq
    @6
    c0
    wceq
    cE
    @28
    c0
    isuvtx.e
    eqeq1i
    cG
    @5
    nbgr0edg
    sylbi
    eleq2d
    ralbidv
    rexbidv
    adantl
    @17
    vv
    cV
    df-rex
    syl6bb
    cV
    cvv
    wcel
    @14
    @21
    wb
    @2
    cV
    cG
    cvtx
    cfv
    cvv
    uvtxel.v
    cG
    cvtx
    fvex
    eqeltri
    cV
    cvv
    vv
    hash1snb
    mp1i
    3bitr4d
    3bitrd
end
