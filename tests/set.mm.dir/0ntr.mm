include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cnt.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "cdif.mm"
include "ssdif0.mm"
include "wi.mm"
include "eqss.mm"
include "fveq2.mm"
include "ntrtop.mm"
include "sylan9eqr.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "syl5bir.mm"
include "expd.mm"
include "com34.mm"
include "imp32.mm"
include "necon3d.mm"
include "imp.mm"
include "an32s.mm"

theorem 0ntr
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ X =/= (/) ) /\ ( S C_ X /\ ( ( int ` J ) ` S ) = (/) ) ) -> ( X \ S ) =/= (/) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cS
    cJ
    cnt
    cfv
    #
    cfv
    #
    c0
    wceq
    #
    wa
    #
    cX
    c0
    wne
    #
    cX
    cS
    cdif
    #
    c0
    wne
    #
    @0
    @5
    wa
    #
    @6
    @8
    @9
    @7
    c0
    cX
    c0
    @7
    c0
    wceq
    cX
    cS
    wss
    #
    @9
    cX
    c0
    wceq
    #
    cX
    cS
    ssdif0
    @0
    @1
    @4
    @10
    @11
    wi
    @0
    @1
    @10
    @4
    @11
    @0
    @1
    @10
    @4
    @11
    wi
    #
    @1
    @10
    wa
    cS
    cX
    wceq
    #
    @0
    @12
    cS
    cX
    eqss
    @0
    @13
    @12
    @0
    @13
    wa
    #
    @4
    @11
    @14
    @3
    cX
    c0
    @13
    @0
    @3
    cX
    @2
    cfv
    cX
    cS
    cX
    @2
    fveq2
    cJ
    cX
    clscld.1
    ntrtop
    sylan9eqr
    eqeq1d
    biimpd
    ex
    syl5bir
    expd
    com34
    imp32
    syl5bir
    necon3d
    imp
    an32s
end
