include "cpw.mm"
include "wss.mm"
include "wtr.mm"
include "wi.mm"
include "wel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wal.mm"
include "wb.mm"
include "dftr2.mm"
include "simpr.mm"
include "ssel.mm"
include "elpwi.mm"
include "syl56.mm"
include "idd.mm"
include "simpl.mm"
include "syl6.mm"
include "syl6c.mm"
include "alrimivv.mm"
include "biimpr.mm"
include "mpsyl.mm"
include "idiALT.mm"

theorem sspwtrALT
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
    cA
    wtr
    #
    wi
    @2
    vz
    vy
    wel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    vz
    cv
    #
    cA
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    #
    wb
    @1
    @10
    @2
    vz
    vy
    cA
    dftr2
    @1
    @9
    vz
    vy
    @1
    @6
    @4
    cA
    wss
    #
    @3
    @8
    @6
    @5
    @1
    @4
    @0
    wcel
    @11
    @3
    @5
    simpr
    cA
    @0
    @4
    ssel
    @4
    cA
    elpwi
    syl56
    @1
    @6
    @6
    @3
    @1
    @6
    idd
    @3
    @5
    simpl
    syl6
    @4
    cA
    @7
    ssel
    syl6c
    alrimivv
    @2
    @10
    biimpr
    mpsyl
    idiALT
end
