include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cdif.mm"
include "cin.mm"
include "cnt.mm"
include "clsdif.mm"
include "ineq2d.mm"
include "indif2.mm"
include "syl6eq.mm"
include "wceq.mm"
include "clsss3.mm"
include "df-ss.mm"
include "sylib.mm"
include "difeq1d.mm"
include "eqtrd.mm"

theorem topbnd
  let cA: class A
  let cJ: class J
  let cX: class X
  assume topbnd.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X ) -> ( ( ( cls ` J ) ` A ) i^i ( ( cls ` J ) ` ( X \ A ) ) ) = ( ( ( cls ` J ) ` A ) \ ( ( int ` J ) ` A ) ) )

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
    ccl
    cfv
    #
    cfv
    #
    cX
    cA
    cdif
    @1
    cfv
    #
    cin
    #
    @2
    cX
    cin
    #
    cA
    cJ
    cnt
    cfv
    cfv
    #
    cdif
    #
    @2
    @6
    cdif
    @0
    @4
    @2
    cX
    @6
    cdif
    #
    cin
    @7
    @0
    @3
    @8
    @2
    cA
    cJ
    cX
    topbnd.1
    clsdif
    ineq2d
    @2
    cX
    @6
    indif2
    syl6eq
    @0
    @5
    @2
    @6
    @0
    @2
    cX
    wss
    @5
    @2
    wceq
    cA
    cJ
    cX
    topbnd.1
    clsss3
    @2
    cX
    df-ss
    sylib
    difeq1d
    eqtrd
end
