include "cpw.mm"
include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "dftr2.mm"
include "wss.mm"
include "idn1.mm"
include "idn2.mm"
include "simpr.mm"
include "e2.mm"
include "pwid.mm"
include "trel.mm"
include "expd.mm"
include "e120.mm"
include "elpwi.mm"
include "simpl.mm"
include "ssel.mm"
include "e22.mm"
include "in2.mm"
include "gen12.mm"
include "biimpr.mm"
include "e01.mm"
include "in1.mm"

theorem pwtrrVD
  let cA: class A
  let vz: setvar z
  let vy: setvar y
  assume pwtrrVD.1: |- A e. _V


  assert |- ( Tr ~P A -> Tr A )

  proof
    cA
    cpw
    #
    wtr
    #
    cA
    wtr
    #
    @2
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    #
    @3
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
    @7
    @8
    @1
    @7
    @4
    cA
    wss
    #
    @5
    @8
    @1
    @7
    @4
    @0
    wcel
    #
    @11
    @1
    @1
    @7
    @6
    cA
    @0
    wcel
    #
    @12
    @1
    idn1
    @1
    @7
    @7
    @6
    @1
    @7
    idn2
    #
    @5
    @6
    simpr
    e2
    cA
    pwtrrVD.1
    pwid
    @1
    @6
    @13
    @12
    @0
    @4
    cA
    trel
    expd
    e120
    @4
    cA
    elpwi
    e2
    @1
    @7
    @7
    @5
    @14
    @5
    @6
    simpl
    e2
    @4
    cA
    @3
    ssel
    e22
    in2
    gen12
    @2
    @10
    biimpr
    e01
    in1
end
