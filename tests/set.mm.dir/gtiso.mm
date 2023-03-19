include "cxr.mm"
include "wss.mm"
include "wa.mm"
include "clt.mm"
include "ccnv.mm"
include "wiso.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "cdif.mm"
include "wb.mm"
include "eqid.mm"
include "isocnv3.mm"
include "a1i.mm"
include "wceq.mm"
include "df-le.mm"
include "cnveqi.mm"
include "cnvdif.mm"
include "cnvxp.mm"
include "wrel.mm"
include "ltrel.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "difeq12i.mm"
include "3eqtri.mm"
include "ineq1i.mm"
include "indif1.mm"
include "eqtri.mm"
include "xpss12.mm"
include "anidms.mm"
include "sseqin2.mm"
include "sylib.mm"
include "difeq1d.mm"
include "syl5req.mm"
include "adantr.mm"
include "isoeq2.mm"
include "syl.mm"
include "adantl.mm"
include "isoeq3.mm"
include "3bitrd.mm"
include "isocnv2.mm"
include "isores2.mm"
include "isores1.mm"
include "bitri.mm"
include "lerel.mm"
include "ax-mp.mm"
include "3bitr3ri.mm"
include "syl6bbr.mm"

theorem gtiso
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( A C_ RR* /\ B C_ RR* ) -> ( F Isom < , `' < ( A , B ) <-> F Isom <_ , `' <_ ( A , B ) ) )

  proof
    cA
    cxr
    wss
    #
    cB
    cxr
    wss
    #
    wa
    #
    cA
    cB
    clt
    clt
    ccnv
    #
    cF
    wiso
    #
    cA
    cB
    cle
    ccnv
    #
    cA
    cA
    cxp
    #
    cin
    #
    cle
    cB
    cB
    cxp
    #
    cin
    #
    cF
    wiso
    #
    cA
    cB
    cle
    @5
    cF
    wiso
    #
    @2
    @4
    cA
    cB
    @6
    clt
    cdif
    #
    @8
    @3
    cdif
    #
    cF
    wiso
    #
    cA
    cB
    @7
    @13
    cF
    wiso
    #
    @10
    @4
    @14
    wb
    @2
    cA
    cB
    @12
    @13
    clt
    @3
    cF
    @12
    eqid
    @13
    eqid
    isocnv3
    a1i
    @2
    @12
    @7
    wceq
    #
    @14
    @15
    wb
    @0
    @16
    @1
    @0
    @7
    cxr
    cxr
    cxp
    #
    @6
    cin
    #
    clt
    cdif
    #
    @12
    @7
    @17
    clt
    cdif
    #
    @6
    cin
    @19
    @5
    @20
    @6
    @5
    @17
    @3
    cdif
    #
    ccnv
    @17
    ccnv
    #
    @3
    ccnv
    #
    cdif
    @20
    cle
    @21
    df-le
    cnveqi
    @17
    @3
    cnvdif
    @22
    @17
    @23
    clt
    cxr
    cxr
    cnvxp
    clt
    wrel
    @23
    clt
    wceq
    ltrel
    clt
    dfrel2
    mpbi
    difeq12i
    3eqtri
    ineq1i
    @17
    @6
    clt
    indif1
    eqtri
    @0
    @18
    @6
    clt
    @0
    @6
    @17
    wss
    #
    @18
    @6
    wceq
    @0
    @24
    cA
    cxr
    cA
    cxr
    xpss12
    anidms
    @6
    @17
    sseqin2
    sylib
    difeq1d
    syl5req
    adantr
    cA
    cB
    @12
    @13
    @7
    cF
    isoeq2
    syl
    @2
    @13
    @9
    wceq
    #
    @15
    @10
    wb
    @1
    @25
    @0
    @1
    @9
    @17
    @8
    cin
    #
    @3
    cdif
    #
    @13
    @9
    @21
    @8
    cin
    @27
    cle
    @21
    @8
    df-le
    ineq1i
    @17
    @8
    @3
    indif1
    eqtri
    @1
    @26
    @8
    @3
    @1
    @8
    @17
    wss
    #
    @26
    @8
    wceq
    @1
    @28
    cB
    cxr
    cB
    cxr
    xpss12
    anidms
    @8
    @17
    sseqin2
    sylib
    difeq1d
    syl5req
    adantl
    cA
    cB
    @7
    @13
    @9
    cF
    isoeq3
    syl
    3bitrd
    cA
    cB
    @5
    cle
    cF
    wiso
    #
    cA
    cB
    @5
    ccnv
    #
    @5
    cF
    wiso
    #
    @10
    @11
    cA
    cB
    @5
    cle
    cF
    isocnv2
    @29
    cA
    cB
    @5
    @9
    cF
    wiso
    @10
    cA
    cB
    @5
    cle
    cF
    isores2
    cA
    cB
    @5
    @9
    cF
    isores1
    bitri
    @30
    cle
    wceq
    #
    @31
    @11
    wb
    cle
    wrel
    @32
    lerel
    cle
    dfrel2
    mpbi
    cA
    cB
    @30
    @5
    cle
    cF
    isoeq2
    ax-mp
    3bitr3ri
    syl6bbr
end
