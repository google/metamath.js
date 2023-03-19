include "c0.mm"
include "cust.mm"
include "cfv.mm"
include "csn.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "isust.mm"
include "ax-mp.mm"
include "simp1bi.mm"
include "0xp.mm"
include "pweqi.mm"
include "pw0.mm"
include "eqtri.mm"
include "syl6sseq.mm"
include "ustbasel.mm"
include "syl5eqelr.mm"
include "snssd.mm"
include "eqssd.mm"
include "velsn.mm"
include "sylibr.mm"
include "ssriv.mm"
include "eqimss2i.mm"
include "snid.mm"
include "eqeltri.mm"
include "a1i.mm"
include "raleqi.mm"
include "sseq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "ralsn.mm"
include "bitri.mm"
include "mpbir.mm"
include "inidm.mm"
include "ineq2.mm"
include "eleq1d.mm"
include "res0.mm"
include "eqimssi.mm"
include "cnv0.mm"
include "0trrel.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq1d.mm"
include "rexsn.mm"
include "3pm3.2i.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "ineq1.mm"
include "cnveq.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "mpbir3an.mm"
include "snssi.mm"
include "eqssi.mm"

theorem ust0
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( UnifOn ` (/) ) = { { (/) } }

  proof
    c0
    cust
    cfv
    #
    c0
    csn
    #
    csn
    #
    vu
    @0
    @2
    vu
    cv
    #
    @0
    wcel
    #
    @3
    @1
    wceq
    @3
    @2
    wcel
    @4
    @3
    @1
    @4
    @3
    c0
    c0
    cxp
    #
    cpw
    #
    @1
    @4
    @3
    @6
    wss
    #
    @5
    @3
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    #
    @10
    @3
    wcel
    wi
    vw
    @6
    wral
    @9
    @10
    cin
    #
    @3
    wcel
    vw
    @3
    wral
    cid
    c0
    cres
    #
    @9
    wss
    #
    @9
    ccnv
    #
    @3
    wcel
    @10
    @10
    ccom
    #
    @9
    wss
    #
    vw
    @3
    wrex
    w3a
    w3a
    vv
    @3
    wral
    #
    c0
    cvv
    wcel
    #
    @4
    @7
    @8
    @18
    w3a
    wb
    0ex
    vw
    vv
    @3
    cvv
    c0
    isust
    ax-mp
    simp1bi
    @6
    c0
    cpw
    @1
    @5
    c0
    c0
    0xp
    #
    pweqi
    pw0
    eqtri
    #
    syl6sseq
    @4
    c0
    @3
    @4
    c0
    @5
    @3
    @20
    @3
    c0
    ustbasel
    syl5eqelr
    snssd
    eqssd
    vu
    @1
    velsn
    sylibr
    ssriv
    @1
    @0
    wcel
    #
    @2
    @0
    wss
    @22
    @1
    @6
    wss
    #
    @5
    @1
    wcel
    #
    @11
    @10
    @1
    wcel
    #
    wi
    #
    vw
    @6
    wral
    #
    @12
    @1
    wcel
    #
    vw
    @1
    wral
    #
    @14
    @15
    @1
    wcel
    #
    @17
    vw
    @1
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    @1
    wral
    #
    @6
    @1
    @21
    eqimss2i
    @5
    c0
    @1
    @20
    c0
    0ex
    snid
    #
    eqeltri
    @34
    c0
    @10
    wss
    #
    @25
    wi
    #
    vw
    @6
    wral
    #
    c0
    @10
    cin
    #
    @1
    wcel
    #
    vw
    @1
    wral
    #
    @13
    c0
    wss
    #
    c0
    ccnv
    #
    @1
    wcel
    #
    @16
    c0
    wss
    #
    vw
    @1
    wrex
    #
    w3a
    #
    @38
    c0
    c0
    wss
    #
    c0
    @1
    wcel
    #
    wi
    #
    @49
    @48
    @35
    a1i
    @38
    @37
    vw
    @1
    wral
    @50
    @37
    vw
    @6
    @1
    @21
    raleqi
    @37
    @50
    vw
    c0
    0ex
    @10
    c0
    wceq
    #
    @36
    @48
    @25
    @49
    @10
    c0
    c0
    sseq2
    @10
    c0
    @1
    eleq1
    imbi12d
    ralsn
    bitri
    mpbir
    @41
    c0
    c0
    cin
    #
    @1
    wcel
    #
    @52
    c0
    @1
    c0
    inidm
    @35
    eqeltri
    @40
    @53
    vw
    c0
    0ex
    @51
    @39
    @52
    @1
    @10
    c0
    c0
    ineq2
    eleq1d
    ralsn
    mpbir
    @42
    @44
    @46
    @13
    c0
    cid
    res0
    eqimssi
    @43
    c0
    @1
    cnv0
    @35
    eqeltri
    @46
    c0
    c0
    ccom
    #
    c0
    wss
    #
    0trrel
    @45
    @55
    vw
    c0
    0ex
    @51
    @16
    @54
    c0
    @51
    @10
    c0
    @10
    c0
    @51
    id
    #
    @56
    coeq12d
    sseq1d
    rexsn
    mpbir
    3pm3.2i
    @33
    @38
    @41
    @47
    w3a
    vv
    c0
    0ex
    @9
    c0
    wceq
    #
    @27
    @38
    @29
    @41
    @32
    @47
    @57
    @26
    @37
    vw
    @6
    @57
    @11
    @36
    @25
    @9
    c0
    @10
    sseq1
    imbi1d
    ralbidv
    @57
    @28
    @40
    vw
    @1
    @57
    @12
    @39
    @1
    @9
    c0
    @10
    ineq1
    eleq1d
    ralbidv
    @57
    @14
    @42
    @30
    @44
    @31
    @46
    @9
    c0
    @13
    sseq2
    @57
    @15
    @43
    @1
    @9
    c0
    cnveq
    eleq1d
    @57
    @17
    @45
    vw
    @1
    @9
    c0
    @16
    sseq2
    rexbidv
    3anbi123d
    3anbi123d
    ralsn
    mpbir3an
    @19
    @22
    @23
    @24
    @34
    w3a
    wb
    0ex
    vw
    vv
    @1
    cvv
    c0
    isust
    ax-mp
    mpbir3an
    @1
    @0
    snssi
    ax-mp
    eqssi
end
