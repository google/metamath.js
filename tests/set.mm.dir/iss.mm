include "cid.mm"
include "wss.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "ssel.mm"
include "wi.mm"
include "vex.mm"
include "opeldm.mm"
include "a1i.mm"
include "jcad.mm"
include "wbr.mm"
include "df-br.mm"
include "ideq.mm"
include "bitr3i.mm"
include "wex.mm"
include "eldm2.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "syl5bi.mm"
include "sylcom.mm"
include "exlimdv.mm"
include "imbi2d.mm"
include "syl5ibcom.mm"
include "impd.mm"
include "impbid.mm"
include "opelres.mm"
include "syl6bbr.mm"
include "alrimivv.mm"
include "wrel.mm"
include "reli.mm"
include "relss.mm"
include "mpi.mm"
include "relres.mm"
include "eqrel.mm"
include "sylancl.mm"
include "mpbird.mm"
include "resss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem iss
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ _I <-> A = ( _I |` dom A ) )

  proof
    cA
    cid
    wss
    #
    cA
    cid
    cA
    cdm
    #
    cres
    #
    wceq
    #
    @0
    @3
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @6
    @2
    wcel
    #
    wb
    #
    vy
    wal
    vx
    wal
    #
    @0
    @9
    vx
    vy
    @0
    @7
    @6
    cid
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @8
    @0
    @7
    @13
    @0
    @7
    @11
    @12
    cA
    cid
    @6
    ssel
    #
    @7
    @12
    wi
    @0
    @4
    @5
    cA
    vx
    vex
    #
    vy
    vex
    #
    opeldm
    a1i
    jcad
    @0
    @11
    @12
    @7
    @11
    @4
    @5
    wceq
    #
    @0
    @12
    @7
    wi
    #
    @11
    @4
    @5
    cid
    wbr
    @17
    @4
    @5
    cid
    df-br
    @4
    @5
    @16
    ideq
    bitr3i
    #
    @0
    @12
    @4
    @4
    cop
    #
    cA
    wcel
    #
    wi
    @17
    @18
    @12
    @7
    vy
    wex
    @0
    @21
    vy
    @4
    cA
    @15
    eldm2
    @0
    @7
    @21
    vy
    @0
    @7
    @11
    @21
    @14
    @11
    @17
    @7
    @21
    @19
    @17
    @21
    @7
    @17
    @20
    @6
    cA
    @4
    @5
    @4
    opeq2
    eleq1d
    #
    biimprcd
    syl5bi
    sylcom
    exlimdv
    syl5bi
    @17
    @21
    @7
    @12
    @22
    imbi2d
    syl5ibcom
    syl5bi
    impd
    impbid
    @4
    @5
    cid
    @1
    @16
    opelres
    syl6bbr
    alrimivv
    @0
    cA
    wrel
    #
    @2
    wrel
    @3
    @10
    wb
    @0
    cid
    wrel
    @23
    reli
    cA
    cid
    relss
    mpi
    cid
    @1
    relres
    vx
    vy
    cA
    @2
    eqrel
    sylancl
    mpbird
    @3
    @0
    @2
    cid
    wss
    cid
    @1
    resss
    cA
    @2
    cid
    sseq1
    mpbiri
    impbii
end
