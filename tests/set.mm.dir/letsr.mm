include "cle.mm"
include "ctsr.mm"
include "wcel.mm"
include "cps.mm"
include "cxr.mm"
include "cxp.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "wrel.mm"
include "ccom.mm"
include "cin.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "lerel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "lerelxr.mm"
include "brel.mm"
include "adantr.mm"
include "simpld.mm"
include "simprd.mm"
include "adantl.mm"
include "3jca.mm"
include "xrletr.mm"
include "mpcom.mm"
include "ax-gen.mm"
include "gen2.mm"
include "cotr.mm"
include "mpbir.mm"
include "wb.mm"
include "asymref.mm"
include "simpr.mm"
include "xrletri3.mm"
include "sylan2.mm"
include "mpbird.mm"
include "ex.mm"
include "xrleid.mm"
include "jca.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "impbid.mm"
include "alrimiv.mm"
include "lefld.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "mprgbir.mm"
include "cvv.mm"
include "xrex.mm"
include "xpex.mm"
include "ssexi.mm"
include "isps.mm"
include "ax-mp.mm"
include "mpbir3an.mm"
include "wo.mm"
include "wral.mm"
include "xrletri.mm"
include "rgen2a.mm"
include "qfto.mm"
include "ledm.mm"
include "istsr.mm"
include "mpbir2an.mm"

theorem letsr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- <_ e. TosetRel

  proof
    cle
    ctsr
    wcel
    cle
    cps
    wcel
    #
    cxr
    cxr
    cxp
    #
    cle
    cle
    ccnv
    #
    cun
    wss
    #
    @0
    cle
    wrel
    #
    cle
    cle
    ccom
    cle
    wss
    #
    cle
    @2
    cin
    cid
    cle
    cuni
    cuni
    #
    cres
    wceq
    #
    lerel
    @5
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @9
    vz
    cv
    #
    cle
    wbr
    #
    wa
    #
    @8
    @11
    cle
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @16
    vx
    vy
    @15
    vz
    @8
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    @11
    cxr
    wcel
    #
    w3a
    @13
    @14
    @13
    @17
    @18
    @19
    @13
    @17
    @18
    @10
    @17
    @18
    wa
    @12
    @8
    @9
    cxr
    cxr
    cle
    lerelxr
    brel
    adantr
    #
    simpld
    @13
    @17
    @18
    @20
    simprd
    @12
    @19
    @10
    @12
    @18
    @19
    @9
    @11
    cxr
    cxr
    cle
    lerelxr
    brel
    simprd
    adantl
    3jca
    @8
    @9
    @11
    xrletr
    mpcom
    ax-gen
    gen2
    vx
    vy
    vz
    cle
    cotr
    mpbir
    @7
    @10
    @9
    @8
    cle
    wbr
    #
    wa
    #
    @8
    @9
    wceq
    #
    wb
    #
    vy
    wal
    #
    vx
    @6
    vx
    vy
    cle
    asymref
    @25
    @8
    cxr
    @6
    @17
    @24
    vy
    @17
    @22
    @23
    @17
    @22
    @23
    @17
    @22
    wa
    @23
    @22
    @17
    @22
    simpr
    @22
    @17
    @18
    @23
    @22
    wb
    @21
    @18
    @10
    @21
    @18
    @17
    @9
    @8
    cxr
    cxr
    cle
    lerelxr
    brel
    simpld
    adantl
    @8
    @9
    xrletri3
    sylan2
    mpbird
    ex
    @17
    @8
    @8
    cle
    wbr
    #
    @26
    wa
    @23
    @22
    @17
    @26
    @26
    @8
    xrleid
    #
    @27
    jca
    @23
    @26
    @10
    @26
    @21
    @8
    @9
    @8
    cle
    breq2
    @8
    @9
    @8
    cle
    breq1
    anbi12d
    syl5ibcom
    impbid
    alrimiv
    cxr
    @6
    lefld
    eqcomi
    eleq2s
    mprgbir
    cle
    cvv
    wcel
    @0
    @4
    @5
    @7
    w3a
    wb
    cle
    @1
    cxr
    cxr
    xrex
    xrex
    xpex
    lerelxr
    ssexi
    cvv
    cle
    isps
    ax-mp
    mpbir3an
    @3
    @10
    @21
    wo
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @28
    vx
    vy
    cxr
    @8
    @9
    xrletri
    rgen2a
    vx
    vy
    cxr
    cxr
    cle
    qfto
    mpbir
    cle
    cxr
    ledm
    istsr
    mpbir2an
end
