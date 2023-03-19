include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "ccl.mm"
include "cfv.mm"
include "cnt.mm"
include "wceq.mm"
include "difss.mm"
include "clsval2.mm"
include "mpan2.mm"
include "adantr.mm"
include "simpr.mm"
include "dfss4.mm"
include "sylib.mm"
include "fveq2d.mm"
include "difeq2d.mm"
include "eqtrd.mm"

theorem clsdif
  let cA: class A
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X ) -> ( ( cls ` J ) ` ( X \ A ) ) = ( X \ ( ( int ` J ) ` A ) ) )

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
    cX
    cA
    cdif
    #
    cJ
    ccl
    cfv
    cfv
    #
    cX
    cX
    @3
    cdif
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    cdif
    #
    cX
    cA
    @6
    cfv
    #
    cdif
    @0
    @4
    @8
    wceq
    #
    @1
    @0
    @3
    cX
    wss
    @10
    cX
    cA
    difss
    @3
    cJ
    cX
    clscld.1
    clsval2
    mpan2
    adantr
    @2
    @7
    @9
    cX
    @2
    @5
    cA
    @6
    @2
    @1
    @5
    cA
    wceq
    @0
    @1
    simpr
    cA
    cX
    dfss4
    sylib
    fveq2d
    difeq2d
    eqtrd
end
