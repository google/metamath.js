include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cnt.mm"
include "cfv.mm"
include "wa.mm"
include "cdif.mm"
include "ccl.mm"
include "sscon.mm"
include "adantl.mm"
include "difss.mm"
include "jctil.mm"
include "clsss.mm"
include "3expb.mm"
include "sylan2.mm"
include "sscond.mm"
include "wceq.mm"
include "sstr2.mm"
include "impcom.mm"
include "ntrval2.mm"
include "adantrr.mm"
include "3sstr4d.mm"
include "3impb.mm"

theorem ntrss
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X /\ T C_ S ) -> ( ( int ` J ) ` T ) C_ ( ( int ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cT
    cS
    wss
    #
    cT
    cJ
    cnt
    cfv
    #
    cfv
    #
    cS
    @3
    cfv
    #
    wss
    @0
    @1
    @2
    wa
    #
    wa
    #
    cX
    cX
    cT
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cdif
    #
    cX
    cX
    cS
    cdif
    #
    @9
    cfv
    #
    cdif
    #
    @4
    @5
    @7
    @13
    @10
    cX
    @6
    @0
    @8
    cX
    wss
    #
    @12
    @8
    wss
    #
    wa
    @13
    @10
    wss
    #
    @6
    @16
    @15
    @2
    @16
    @1
    cT
    cS
    cX
    sscon
    adantl
    cX
    cT
    difss
    jctil
    @0
    @15
    @16
    @17
    @8
    @12
    cJ
    cX
    clscld.1
    clsss
    3expb
    sylan2
    sscond
    @6
    @0
    cT
    cX
    wss
    #
    @4
    @11
    wceq
    @2
    @1
    @18
    cT
    cS
    cX
    sstr2
    impcom
    cT
    cJ
    cX
    clscld.1
    ntrval2
    sylan2
    @0
    @1
    @5
    @14
    wceq
    @2
    cS
    cJ
    cX
    clscld.1
    ntrval2
    adantrr
    3sstr4d
    3impb
end
