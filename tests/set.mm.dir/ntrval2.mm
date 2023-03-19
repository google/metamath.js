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
include "dfss4.mm"
include "biimpi.mm"
include "fveq2d.mm"
include "adantl.mm"
include "difeq2d.mm"
include "eqtrd.mm"
include "ntropn.mm"
include "eltopss.mm"
include "syldan.mm"
include "sylib.mm"
include "eqtr2d.mm"

theorem ntrval2
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( int ` J ) ` S ) = ( X \ ( ( cls ` J ) ` ( X \ S ) ) ) )

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
    cX
    cS
    cdif
    #
    cJ
    ccl
    cfv
    cfv
    #
    cdif
    cX
    cX
    cS
    cJ
    cnt
    cfv
    #
    cfv
    #
    cdif
    #
    cdif
    #
    @6
    @2
    @4
    @7
    cX
    @2
    @4
    cX
    cX
    @3
    cdif
    #
    @5
    cfv
    #
    cdif
    #
    @7
    @0
    @4
    @11
    wceq
    #
    @1
    @0
    @3
    cX
    wss
    @12
    cX
    cS
    difss
    @3
    cJ
    cX
    clscld.1
    clsval2
    mpan2
    adantr
    @2
    @10
    @6
    cX
    @1
    @10
    @6
    wceq
    @0
    @1
    @9
    cS
    @5
    @1
    @9
    cS
    wceq
    cS
    cX
    dfss4
    biimpi
    fveq2d
    adantl
    difeq2d
    eqtrd
    difeq2d
    @2
    @6
    cX
    wss
    #
    @8
    @6
    wceq
    @0
    @1
    @6
    cJ
    wcel
    @13
    cS
    cJ
    cX
    clscld.1
    ntropn
    @6
    cJ
    cX
    clscld.1
    eltopss
    syldan
    @6
    cX
    dfss4
    sylib
    eqtr2d
end
