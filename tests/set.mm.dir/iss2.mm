include "cid.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "ssel.mm"
include "vex.mm"
include "opeldm.mm"
include "jca2.mm"
include "opelrn.mm"
include "jcad.mm"
include "anandi.mm"
include "syl6ibr.mm"
include "wi.mm"
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
include "imp.mm"
include "adantrd.mm"
include "ex.mm"
include "impd.mm"
include "impbid.mm"
include "opelinxp.mm"
include "biancom.mm"
include "syl6bbr.mm"
include "alrimivv.mm"
include "wrel.mm"
include "reli.mm"
include "relss.mm"
include "mpi.mm"
include "relinxp.mm"
include "eqrel.mm"
include "sylancl.mm"
include "mpbird.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem iss2
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ _I <-> A = ( _I i^i ( dom A X. ran A ) ) )

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
    cA
    crn
    #
    cxp
    #
    cin
    #
    wceq
    #
    @0
    @5
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
    @8
    @4
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
    @11
    vx
    vy
    @0
    @9
    @8
    cid
    wcel
    #
    @6
    @1
    wcel
    #
    @7
    @2
    wcel
    #
    wa
    #
    wa
    #
    @10
    @0
    @9
    @17
    @0
    @9
    @13
    @14
    wa
    #
    @13
    @15
    wa
    #
    wa
    @17
    @0
    @9
    @18
    @19
    @0
    @9
    @13
    @14
    cA
    cid
    @8
    ssel
    #
    @6
    @7
    cA
    vx
    vex
    #
    vy
    vex
    #
    opeldm
    jca2
    @0
    @9
    @13
    @15
    @20
    @6
    @7
    cA
    @21
    @22
    opelrn
    jca2
    jcad
    @13
    @14
    @15
    anandi
    syl6ibr
    @0
    @13
    @16
    @9
    @13
    @6
    @7
    wceq
    #
    @0
    @16
    @9
    wi
    #
    @13
    @6
    @7
    cid
    wbr
    @23
    @6
    @7
    cid
    df-br
    @6
    @7
    @22
    ideq
    bitr3i
    #
    @0
    @23
    @24
    @0
    @23
    wa
    @14
    @9
    @15
    @0
    @23
    @14
    @9
    wi
    #
    @0
    @14
    @6
    @6
    cop
    #
    cA
    wcel
    #
    wi
    @23
    @26
    @14
    @9
    vy
    wex
    @0
    @28
    vy
    @6
    cA
    @21
    eldm2
    @0
    @9
    @28
    vy
    @0
    @9
    @13
    @28
    @20
    @13
    @23
    @9
    @28
    @25
    @23
    @28
    @9
    @23
    @27
    @8
    cA
    @6
    @7
    @6
    opeq2
    eleq1d
    #
    biimprcd
    syl5bi
    sylcom
    exlimdv
    syl5bi
    @23
    @28
    @9
    @14
    @29
    imbi2d
    syl5ibcom
    imp
    adantrd
    ex
    syl5bi
    impd
    impbid
    @10
    @13
    @16
    @1
    @2
    @6
    @7
    cid
    opelinxp
    biancom
    syl6bbr
    alrimivv
    @0
    cA
    wrel
    #
    @4
    wrel
    @5
    @12
    wb
    @0
    cid
    wrel
    @30
    reli
    cA
    cid
    relss
    mpi
    @1
    @2
    cid
    relinxp
    vx
    vy
    cA
    @4
    eqrel
    sylancl
    mpbird
    @5
    @0
    @4
    cid
    wss
    cid
    @3
    inss1
    cA
    @4
    cid
    sseq1
    mpbiri
    impbii
end
