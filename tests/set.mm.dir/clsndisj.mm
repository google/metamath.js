include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "simp1.mm"
include "simp2.mm"
include "clsss3.mm"
include "sseld.mm"
include "3impia.mm"
include "simp3.mm"
include "elcls.mm"
include "biimpa.mm"
include "syl31anc.mm"
include "wceq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "imp32.mm"
include "sylan.mm"

theorem clsndisj
  let cP: class P
  let cS: class S
  let cU: class U
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ S C_ X /\ P e. ( ( cls ` J ) ` S ) ) /\ ( U e. J /\ P e. U ) ) -> ( U i^i S ) =/= (/) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    w3a
    #
    cP
    vx
    cv
    #
    wcel
    #
    @5
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vx
    cJ
    wral
    #
    cU
    cJ
    wcel
    #
    cP
    cU
    wcel
    #
    wa
    cU
    cS
    cin
    #
    c0
    wne
    #
    @4
    @0
    @1
    cP
    cX
    wcel
    #
    @3
    @10
    @0
    @1
    @3
    simp1
    @0
    @1
    @3
    simp2
    @0
    @1
    @3
    @15
    @0
    @1
    wa
    @2
    cX
    cP
    cS
    cJ
    cX
    clscld.1
    clsss3
    sseld
    3impia
    @0
    @1
    @3
    simp3
    @0
    @1
    @15
    w3a
    @3
    @10
    vx
    cP
    cS
    cJ
    cX
    clscld.1
    elcls
    biimpa
    syl31anc
    @10
    @11
    @12
    @14
    @9
    @12
    @14
    wi
    vx
    cU
    cJ
    @5
    cU
    wceq
    #
    @6
    @12
    @8
    @14
    @5
    cU
    cP
    eleq2
    @16
    @7
    @13
    c0
    @5
    cU
    cS
    ineq1
    neeq1d
    imbi12d
    rspccv
    imp32
    sylan
end
