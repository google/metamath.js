include "cxr.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "clt.mm"
include "ccnv.mm"
include "cdif.mm"
include "wiso.mm"
include "cle.mm"
include "cin.mm"
include "wceq.mm"
include "wb.mm"
include "df-le.mm"
include "ineq1i.mm"
include "indif1.mm"
include "eqtri.mm"
include "xpss12.mm"
include "anidms.mm"
include "sseqin2.mm"
include "sylib.mm"
include "difeq1d.mm"
include "syl5req.mm"
include "isoeq2.mm"
include "syl.mm"
include "isoeq3.mm"
include "sylan9bb.mm"
include "isocnv2.mm"
include "eqid.mm"
include "isocnv3.mm"
include "bitri.mm"
include "isores1.mm"
include "isores2.mm"
include "3bitr4g.mm"

theorem leiso
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( A C_ RR* /\ B C_ RR* ) -> ( F Isom < , < ( A , B ) <-> F Isom <_ , <_ ( A , B ) ) )

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
    cA
    cB
    cA
    cA
    cxp
    #
    clt
    ccnv
    #
    cdif
    #
    cB
    cB
    cxp
    #
    @3
    cdif
    #
    cF
    wiso
    #
    cA
    cB
    cle
    @2
    cin
    #
    cle
    @5
    cin
    #
    cF
    wiso
    #
    cA
    cB
    clt
    clt
    cF
    wiso
    #
    cA
    cB
    cle
    cle
    cF
    wiso
    #
    @0
    @7
    cA
    cB
    @8
    @6
    cF
    wiso
    #
    @1
    @10
    @0
    @4
    @8
    wceq
    @7
    @13
    wb
    @0
    @8
    cxr
    cxr
    cxp
    #
    @2
    cin
    #
    @3
    cdif
    #
    @4
    @8
    @14
    @3
    cdif
    #
    @2
    cin
    @16
    cle
    @17
    @2
    df-le
    ineq1i
    @14
    @2
    @3
    indif1
    eqtri
    @0
    @15
    @2
    @3
    @0
    @2
    @14
    wss
    #
    @15
    @2
    wceq
    @0
    @18
    cA
    cxr
    cA
    cxr
    xpss12
    anidms
    @2
    @14
    sseqin2
    sylib
    difeq1d
    syl5req
    cA
    cB
    @4
    @6
    @8
    cF
    isoeq2
    syl
    @1
    @6
    @9
    wceq
    @13
    @10
    wb
    @1
    @9
    @14
    @5
    cin
    #
    @3
    cdif
    #
    @6
    @9
    @17
    @5
    cin
    @20
    cle
    @17
    @5
    df-le
    ineq1i
    @14
    @5
    @3
    indif1
    eqtri
    @1
    @19
    @5
    @3
    @1
    @5
    @14
    wss
    #
    @19
    @5
    wceq
    @1
    @21
    cB
    cxr
    cB
    cxr
    xpss12
    anidms
    @5
    @14
    sseqin2
    sylib
    difeq1d
    syl5req
    cA
    cB
    @8
    @6
    @9
    cF
    isoeq3
    syl
    sylan9bb
    @11
    cA
    cB
    @3
    @3
    cF
    wiso
    @7
    cA
    cB
    clt
    clt
    cF
    isocnv2
    cA
    cB
    @4
    @6
    @3
    @3
    cF
    @4
    eqid
    @6
    eqid
    isocnv3
    bitri
    @12
    cA
    cB
    @8
    cle
    cF
    wiso
    @10
    cA
    cB
    cle
    cle
    cF
    isores1
    cA
    cB
    @8
    cle
    cF
    isores2
    bitri
    3bitr4g
end
