include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cwun.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "wa.mm"
include "tskuni.mm"
include "3expa.mm"
include "3adantl3.mm"
include "tskpw.mm"
include "3ad2antl1.mm"
include "wi.mm"
include "tskpr.mm"
include "3exp.mm"
include "3ad2ant1.mm"
include "imp31.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "wb.mm"
include "iswun.mm"
include "mpbir3and.mm"

theorem tskwun
  let cT: class T
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ Tr T /\ T =/= (/) ) -> T e. WUni )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    cT
    c0
    wne
    #
    w3a
    #
    cT
    cwun
    wcel
    #
    @1
    @2
    vx
    cv
    #
    cuni
    cT
    wcel
    #
    @5
    cpw
    cT
    wcel
    #
    @5
    vy
    cv
    #
    cpr
    cT
    wcel
    #
    vy
    cT
    wral
    #
    w3a
    #
    vx
    cT
    wral
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    @11
    vx
    cT
    @3
    @5
    cT
    wcel
    #
    wa
    #
    @6
    @7
    @10
    @0
    @1
    @13
    @6
    @2
    @0
    @1
    @13
    @6
    @5
    cT
    tskuni
    3expa
    3adantl3
    @0
    @1
    @13
    @7
    @2
    @5
    cT
    tskpw
    3ad2antl1
    @14
    @9
    vy
    cT
    @3
    @13
    @8
    cT
    wcel
    #
    @9
    @0
    @1
    @13
    @15
    @9
    wi
    wi
    @2
    @0
    @13
    @15
    @9
    @5
    @8
    cT
    tskpr
    3exp
    3ad2ant1
    imp31
    ralrimiva
    3jca
    ralrimiva
    @0
    @1
    @4
    @1
    @2
    @12
    w3a
    wb
    @2
    vx
    vy
    cT
    ctsk
    iswun
    3ad2ant1
    mpbir3and
end
