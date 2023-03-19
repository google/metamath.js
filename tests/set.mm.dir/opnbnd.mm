include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "ccl.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "a1i.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "ntrss2.mm"
include "adantr.mm"
include "inssdif0.mm"
include "sscls.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqcomd.mm"
include "eqimss.mm"
include "syl.mm"
include "sstr.mm"
include "sylan.mm"
include "sylan2br.mm"
include "eqssd.mm"
include "ex.mm"
include "impbid.mm"
include "isopn3.mm"
include "topbnd.mm"
include "ineq2d.mm"
include "3bitr4d.mm"

theorem opnbnd
  let cA: class A
  let cJ: class J
  let cX: class X
  assume opnbnd.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X ) -> ( A e. J <-> ( A i^i ( ( ( cls ` J ) ` A ) i^i ( ( cls ` J ) ` ( X \ A ) ) ) ) = (/) ) )

  proof
    cJ
    ctop
    wcel
    cA
    cX
    wss
    wa
    #
    cA
    cJ
    cnt
    cfv
    cfv
    #
    cA
    wceq
    #
    cA
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    @1
    cdif
    #
    cin
    #
    c0
    wceq
    #
    cA
    cJ
    wcel
    cA
    @4
    cX
    cA
    cdif
    @3
    cfv
    cin
    #
    cin
    #
    c0
    wceq
    @0
    @2
    @7
    @0
    @1
    @5
    cin
    #
    c0
    wceq
    #
    @2
    @7
    @11
    @0
    @1
    @4
    disjdif
    a1i
    @2
    @10
    @6
    c0
    @1
    cA
    @5
    ineq1
    eqeq1d
    syl5ibcom
    @0
    @7
    @2
    @0
    @7
    wa
    @1
    cA
    @0
    @1
    cA
    wss
    @7
    cA
    cJ
    cX
    opnbnd.1
    ntrss2
    adantr
    @7
    @0
    cA
    @4
    cin
    #
    @1
    wss
    #
    cA
    @1
    wss
    #
    cA
    @4
    @1
    inssdif0
    @0
    cA
    @12
    wss
    #
    @13
    @14
    @0
    cA
    @12
    wceq
    @15
    @0
    @12
    cA
    @0
    cA
    @4
    wss
    @12
    cA
    wceq
    cA
    cJ
    cX
    opnbnd.1
    sscls
    cA
    @4
    df-ss
    sylib
    eqcomd
    cA
    @12
    eqimss
    syl
    cA
    @12
    @1
    sstr
    sylan
    sylan2br
    eqssd
    ex
    impbid
    cA
    cJ
    cX
    opnbnd.1
    isopn3
    @0
    @9
    @6
    c0
    @0
    @8
    @5
    cA
    cA
    cJ
    cX
    opnbnd.1
    topbnd
    ineq2d
    eqeq1d
    3bitr4d
end
