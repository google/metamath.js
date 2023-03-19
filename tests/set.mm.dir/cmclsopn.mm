include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cdif.mm"
include "cnt.mm"
include "clsval2.mm"
include "difeq2d.mm"
include "wceq.mm"
include "difss.mm"
include "ntropn.mm"
include "mpan2.mm"
include "eltopss.mm"
include "mpdan.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "adantr.mm"

theorem cmclsopn
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( X \ ( ( cls ` J ) ` S ) ) e. J )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cX
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cdif
    cX
    cX
    cX
    cS
    cdif
    #
    cJ
    cnt
    cfv
    cfv
    #
    cdif
    #
    cdif
    #
    cJ
    @2
    @3
    @6
    cX
    cS
    cJ
    cX
    clscld.1
    clsval2
    difeq2d
    @0
    @7
    cJ
    wcel
    @1
    @0
    @7
    @5
    cJ
    @0
    @5
    cX
    wss
    #
    @7
    @5
    wceq
    @0
    @5
    cJ
    wcel
    #
    @8
    @0
    @4
    cX
    wss
    @9
    cX
    cS
    difss
    @4
    cJ
    cX
    clscld.1
    ntropn
    mpan2
    #
    @5
    cJ
    cX
    clscld.1
    eltopss
    mpdan
    @5
    cX
    dfss4
    sylib
    @10
    eqeltrd
    adantr
    eqeltrd
end
