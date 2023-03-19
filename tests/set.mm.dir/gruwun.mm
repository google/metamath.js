include "cgru.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cwun.mm"
include "wtr.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "grutr.mm"
include "adantr.mm"
include "simpr.mm"
include "gruuni.mm"
include "adantlr.mm"
include "grupw.mm"
include "grupr.mm"
include "3expa.mm"
include "adantllr.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "wb.mm"
include "iswun.mm"
include "mpbir3and.mm"

theorem gruwun
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( U e. Univ /\ U =/= (/) ) -> U e. WUni )

  proof
    cU
    cgru
    wcel
    #
    cU
    c0
    wne
    #
    wa
    #
    cU
    cwun
    wcel
    #
    cU
    wtr
    #
    @1
    vx
    cv
    #
    cuni
    cU
    wcel
    #
    @5
    cpw
    cU
    wcel
    #
    @5
    vy
    cv
    #
    cpr
    cU
    wcel
    #
    vy
    cU
    wral
    #
    w3a
    #
    vx
    cU
    wral
    #
    @0
    @4
    @1
    cU
    grutr
    adantr
    @0
    @1
    simpr
    @2
    @11
    vx
    cU
    @2
    @5
    cU
    wcel
    #
    wa
    #
    @6
    @7
    @10
    @0
    @13
    @6
    @1
    @5
    cU
    gruuni
    adantlr
    @0
    @13
    @7
    @1
    @5
    cU
    grupw
    adantlr
    @14
    @9
    vy
    cU
    @0
    @13
    @8
    cU
    wcel
    #
    @9
    @1
    @0
    @13
    @15
    @9
    @5
    @8
    cU
    grupr
    3expa
    adantllr
    ralrimiva
    3jca
    ralrimiva
    @0
    @3
    @4
    @1
    @12
    w3a
    wb
    @1
    vx
    vy
    cU
    cgru
    iswun
    adantr
    mpbir3and
end
