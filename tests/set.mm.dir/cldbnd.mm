include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "ccl.mm"
include "cdif.mm"
include "cin.mm"
include "wceq.mm"
include "iscld3.mm"
include "eqimss.mm"
include "syl6bi.mm"
include "ssinss1.mm"
include "syl6.mm"
include "c0.mm"
include "sslin.mm"
include "adantl.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "sseq0.mm"
include "sylancl.mm"
include "ex.mm"
include "dfss4.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "sylbi.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "wb.mm"
include "difss.mm"
include "opnbnd.mm"
include "mpan2.mm"
include "adantr.mm"
include "bitr4d.mm"
include "wi.mm"
include "opncld.mm"
include "eleq1.mm"
include "sylibd.mm"
include "sylbid.mm"
include "syld.mm"
include "impbid.mm"

theorem cldbnd
  let cA: class A
  let cJ: class J
  let cX: class X
  assume opnbnd.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X ) -> ( A e. ( Clsd ` J ) <-> ( ( ( cls ` J ) ` A ) i^i ( ( cls ` J ) ` ( X \ A ) ) ) C_ A ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cA
    cJ
    ccld
    cfv
    #
    wcel
    #
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    cX
    cA
    cdif
    #
    @5
    cfv
    #
    cin
    #
    cA
    wss
    #
    @2
    @4
    @6
    cA
    wss
    #
    @10
    @2
    @4
    @6
    cA
    wceq
    @11
    cA
    cJ
    cX
    opnbnd.1
    iscld3
    @6
    cA
    eqimss
    syl6bi
    @6
    @8
    cA
    ssinss1
    syl6
    @2
    @10
    @7
    @9
    cin
    #
    c0
    wceq
    #
    @4
    @2
    @10
    @13
    @2
    @10
    wa
    @12
    @7
    cA
    cin
    #
    wss
    #
    @14
    c0
    wceq
    @13
    @10
    @15
    @2
    @9
    cA
    @7
    sslin
    adantl
    @14
    cA
    @7
    cin
    c0
    @7
    cA
    incom
    cA
    cX
    disjdif
    eqtri
    @12
    @14
    sseq0
    sylancl
    ex
    @2
    @13
    @7
    cJ
    wcel
    #
    @4
    @2
    @13
    @7
    @8
    cX
    @7
    cdif
    #
    @5
    cfv
    #
    cin
    #
    cin
    #
    c0
    wceq
    #
    @16
    @2
    @12
    @20
    c0
    @2
    @9
    @19
    @7
    @2
    @9
    @8
    @6
    cin
    @19
    @6
    @8
    incom
    @2
    @6
    @18
    @8
    @1
    @6
    @18
    wceq
    #
    @0
    @1
    @17
    cA
    wceq
    #
    @22
    cA
    cX
    dfss4
    #
    @23
    @18
    @6
    @17
    cA
    @5
    fveq2
    eqcomd
    sylbi
    adantl
    ineq2d
    syl5eq
    ineq2d
    eqeq1d
    @0
    @16
    @21
    wb
    #
    @1
    @0
    @7
    cX
    wss
    @25
    cX
    cA
    difss
    @7
    cJ
    cX
    opnbnd.1
    opnbnd
    mpan2
    adantr
    bitr4d
    @2
    @16
    @17
    @3
    wcel
    #
    @4
    @0
    @16
    @26
    wi
    @1
    @0
    @16
    @26
    @7
    cJ
    cX
    opnbnd.1
    opncld
    ex
    adantr
    @1
    @26
    @4
    wb
    #
    @0
    @1
    @23
    @27
    @24
    @17
    cA
    @3
    eleq1
    sylbi
    adantl
    sylibd
    sylbid
    syld
    impbid
end
