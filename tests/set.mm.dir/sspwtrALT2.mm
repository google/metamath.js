include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wtr.mm"
include "ssel.mm"
include "adantld.mm"
include "elpwi.mm"
include "syl6.mm"
include "simpl.mm"
include "a1i.mm"
include "syl6c.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem sspwtrALT2
  let cA: class A
  let vz: setvar z
  let vy: setvar y


  assert |- ( A C_ ~P A -> Tr A )

  proof
    cA
    cA
    cpw
    #
    wss
    #
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    #
    @2
    cA
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    cA
    wtr
    @1
    @8
    vz
    vy
    @1
    @6
    @3
    cA
    wss
    #
    @4
    @7
    @1
    @6
    @3
    @0
    wcel
    #
    @9
    @1
    @5
    @10
    @4
    cA
    @0
    @3
    ssel
    adantld
    @3
    cA
    elpwi
    syl6
    @6
    @4
    wi
    @1
    @4
    @5
    simpl
    a1i
    @3
    cA
    @2
    ssel
    syl6c
    alrimivv
    vz
    vy
    cA
    dftr2
    sylibr
end
