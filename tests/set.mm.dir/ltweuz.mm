include "cuz.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "clt.mm"
include "wwe.mm"
include "cz.mm"
include "com.mm"
include "cep.mm"
include "word.mm"
include "ordom.mm"
include "ordwe.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "ccnv.mm"
include "wiso.mm"
include "cima.mm"
include "wal.mm"
include "wi.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "rdgeq2.mm"
include "reseq1d.mm"
include "isoeq1.mm"
include "syl.mm"
include "fveq2.mm"
include "isoeq5.mm"
include "0z.mm"
include "elimel.mm"
include "eqid.mm"
include "om2uzisoi.mm"
include "dedth2v.mm"
include "isocnv.mm"
include "cin.mm"
include "dmres.mm"
include "omex.mm"
include "inex1.mm"
include "eqeltri.mm"
include "cnvimass.mm"
include "ssexi.mm"
include "ax-gen.mm"
include "isowe2.mm"
include "sylancl.mm"
include "mpi.mm"
include "cpw.mm"
include "uzf.mm"
include "fdmi.mm"
include "eleq2s.mm"
include "wn.mm"
include "c0.mm"
include "we0.mm"
include "ndmfv.mm"
include "weeq2.mm"
include "mpbiri.mm"
include "pm2.61i.mm"

theorem ltweuz
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- < We ( ZZ>= ` A )

  proof
    cA
    cuz
    cdm
    #
    wcel
    #
    cA
    cuz
    cfv
    #
    clt
    wwe
    #
    @3
    cA
    cz
    @0
    cA
    cz
    wcel
    #
    com
    cep
    wwe
    #
    @3
    com
    word
    @5
    ordom
    com
    ordwe
    ax-mp
    @4
    @2
    com
    clt
    cep
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    cA
    crdg
    #
    com
    cres
    #
    ccnv
    #
    wiso
    #
    @9
    vy
    cv
    #
    cima
    #
    cvv
    wcel
    #
    vy
    wal
    @5
    @3
    wi
    @4
    com
    @2
    cep
    clt
    @8
    wiso
    #
    @10
    @4
    @14
    com
    @2
    cep
    clt
    @6
    @4
    cA
    cc0
    cif
    #
    crdg
    #
    com
    cres
    #
    wiso
    #
    com
    @15
    cuz
    cfv
    #
    cep
    clt
    @17
    wiso
    #
    cA
    cA
    cc0
    cc0
    cA
    @15
    wceq
    #
    @8
    @17
    wceq
    @14
    @18
    wb
    @21
    @7
    @16
    com
    cA
    @15
    @6
    rdgeq2
    reseq1d
    com
    @2
    cep
    clt
    @17
    @8
    isoeq1
    syl
    @21
    @2
    @19
    wceq
    @18
    @20
    wb
    cA
    @15
    cuz
    fveq2
    com
    @2
    @19
    cep
    clt
    @17
    isoeq5
    syl
    vx
    @15
    @17
    cA
    cc0
    cz
    0z
    elimel
    @17
    eqid
    om2uzisoi
    dedth2v
    com
    @2
    cep
    clt
    @8
    isocnv
    syl
    @13
    vy
    @12
    @8
    cdm
    #
    @22
    com
    @7
    cdm
    #
    cin
    cvv
    @7
    com
    dmres
    com
    @23
    omex
    inex1
    eqeltri
    @8
    @11
    cnvimass
    ssexi
    ax-gen
    vy
    @2
    com
    clt
    cep
    @9
    isowe2
    sylancl
    mpi
    cz
    cz
    cpw
    cuz
    uzf
    fdmi
    eleq2s
    @1
    wn
    #
    @3
    c0
    clt
    wwe
    #
    clt
    we0
    @24
    @2
    c0
    wceq
    @3
    @25
    wb
    cA
    cuz
    ndmfv
    @2
    c0
    clt
    weeq2
    syl
    mpbiri
    pm2.61i
end
