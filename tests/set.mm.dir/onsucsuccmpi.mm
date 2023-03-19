include "csuc.mm"
include "ccmp.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "con0.mm"
include "onsuci.mm"
include "onsuctop.mm"
include "ax-mp.mm"
include "wn.mm"
include "wss.mm"
include "onirri.mm"
include "onsucssi.mm"
include "mtbi.mm"
include "sseq1.mm"
include "mtbii.mm"
include "elpwi.mm"
include "unissd.mm"
include "onunisuci.mm"
include "syl6sseq.mm"
include "nsyl.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "cdif.mm"
include "eldif.mm"
include "elpwunsn.mm"
include "sylbir.mm"
include "ex.mm"
include "df-suc.mm"
include "pweqi.mm"
include "eleq2s.mm"
include "snelpwi.mm"
include "snfi.mm"
include "jctr.mm"
include "elin.mm"
include "sylibr.mm"
include "elexi.mm"
include "unisn.mm"
include "eqcomi.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "syl.mm"
include "syl56.mm"
include "rgen.mm"
include "iscmp.mm"
include "mpbir2an.mm"

theorem onsucsuccmpi
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume onsucsuccmpi.1: |- A e. On


  assert |- suc suc A e. Comp

  proof
    cA
    csuc
    #
    csuc
    #
    ccmp
    wcel
    @1
    ctop
    wcel
    #
    @0
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @0
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    @3
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    @1
    cpw
    #
    wral
    @0
    con0
    wcel
    @2
    cA
    onsucsuccmpi.1
    onsuci
    #
    @0
    onsuctop
    ax-mp
    @12
    vy
    @13
    @5
    @3
    @0
    cpw
    #
    wcel
    #
    wn
    #
    @3
    @13
    wcel
    @0
    @3
    wcel
    #
    @11
    @5
    @4
    cA
    wss
    #
    @16
    @5
    @0
    cA
    wss
    #
    @19
    cA
    cA
    wcel
    @20
    cA
    onsucsuccmpi.1
    onirri
    cA
    cA
    onsucsuccmpi.1
    onsucsuccmpi.1
    onsucssi
    mtbi
    @0
    @4
    cA
    sseq1
    mtbii
    @16
    @4
    @0
    cuni
    cA
    @16
    @3
    @0
    @3
    @0
    elpwi
    unissd
    cA
    onsucsuccmpi.1
    onunisuci
    syl6sseq
    nsyl
    @17
    @18
    wi
    @3
    @0
    @0
    csn
    #
    cun
    #
    cpw
    #
    @13
    @3
    @23
    wcel
    #
    @17
    @18
    @24
    @17
    wa
    @3
    @23
    @15
    cdif
    wcel
    @18
    @3
    @23
    @15
    eldif
    @3
    @0
    @0
    elpwunsn
    sylbir
    ex
    @1
    @22
    @0
    df-suc
    pweqi
    eleq2s
    @18
    @21
    @9
    wcel
    #
    @11
    @0
    @3
    snelpwi
    @25
    @21
    @10
    wcel
    #
    @0
    @21
    cuni
    #
    wceq
    #
    @11
    @25
    @25
    @21
    cfn
    wcel
    #
    wa
    @26
    @25
    @29
    @0
    snfi
    jctr
    @21
    @9
    cfn
    elin
    sylibr
    @27
    @0
    @0
    @0
    con0
    @14
    elexi
    unisn
    eqcomi
    @8
    @28
    vz
    @21
    @10
    @6
    @21
    wceq
    @7
    @27
    @0
    @6
    @21
    unieq
    eqeq2d
    rspcev
    sylancl
    syl
    syl56
    rgen
    vy
    vz
    @1
    @0
    @1
    cuni
    @0
    @0
    @14
    onunisuci
    eqcomi
    iscmp
    mpbir2an
end
