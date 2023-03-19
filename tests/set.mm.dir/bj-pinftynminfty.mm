include "cpinfty.mm"
include "cminfty.mm"
include "wceq.mm"
include "cc0.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "cpi.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "nesymi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "wb.mm"
include "cxr.mm"
include "cr.mm"
include "renegcli.mm"
include "rexri.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "0red.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "a1i.mm"
include "0re.mm"
include "ltleii.mm"
include "elioc2.mm"
include "mpbir3and.mm"
include "mp2an.mm"
include "simpr.mm"
include "lttri.mm"
include "leidi.mm"
include "bj-inftyexpiinj.mm"
include "mtbi.mm"
include "df-bj-minfty.mm"
include "eqeq2i.mm"
include "mtbir.mm"
include "df-bj-pinfty.mm"
include "eqeq1i.mm"
include "neir.mm"

theorem bj-pinftynminfty



  assert |- pinfty =/= minfty

  proof
    cpinfty
    cminfty
    cpinfty
    cminfty
    wceq
    cc0
    cinftyexpi
    cfv
    #
    cminfty
    wceq
    #
    @1
    @0
    cpi
    cinftyexpi
    cfv
    #
    wceq
    #
    cc0
    cpi
    wceq
    #
    @3
    cpi
    cc0
    cpi
    pire
    pipos
    gt0ne0ii
    nesymi
    cc0
    cpi
    cneg
    #
    cpi
    cioc
    co
    #
    wcel
    #
    cpi
    @6
    wcel
    #
    @4
    @3
    wb
    @5
    cxr
    wcel
    #
    cpi
    cr
    wcel
    #
    @7
    @5
    cpi
    pire
    renegcli
    #
    rexri
    #
    pire
    @9
    @10
    wa
    #
    @7
    cc0
    cr
    wcel
    @5
    cc0
    clt
    wbr
    #
    cc0
    cpi
    cle
    wbr
    #
    @13
    0red
    @14
    @13
    cc0
    cpi
    clt
    wbr
    #
    @14
    pipos
    @10
    @16
    @14
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
    #
    a1i
    @15
    @13
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    a1i
    @5
    cpi
    cc0
    elioc2
    mpbir3and
    mp2an
    @9
    @10
    @8
    @12
    pire
    @13
    @8
    @10
    @5
    cpi
    clt
    wbr
    #
    cpi
    cpi
    cle
    wbr
    #
    @9
    @10
    simpr
    @18
    @13
    @14
    @16
    @18
    @17
    pipos
    @5
    cc0
    cpi
    @11
    0re
    pire
    lttri
    mp2an
    a1i
    @19
    @13
    cpi
    pire
    leidi
    a1i
    @5
    cpi
    cpi
    elioc2
    mpbir3and
    mp2an
    cc0
    cpi
    bj-inftyexpiinj
    mp2an
    mtbi
    cminfty
    @2
    @0
    df-bj-minfty
    eqeq2i
    mtbir
    cpinfty
    @0
    cminfty
    df-bj-pinfty
    eqeq1i
    mtbir
    neir
end
