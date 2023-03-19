include "wtr.mm"
include "cpw.mm"
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
include "elpwi.mm"
include "simpl.mm"
include "ssel.mm"
include "e22.mm"
include "trss.mm"
include "e12.mm"
include "vex.mm"
include "elpw.mm"
include "e2bir.mm"
include "in2.mm"
include "gen12.mm"
include "biimpr.mm"
include "e01.mm"
include "in1.mm"

theorem pwtrVD
  let cA: class A
  let vz: setvar z
  let vy: setvar y


  assert |- ( Tr A -> Tr ~P A )

  proof
    cA
    wtr
    #
    cA
    cpw
    #
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
    @1
    wcel
    #
    wa
    #
    @3
    @1
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
    @0
    @10
    @2
    vz
    vy
    @1
    dftr2
    @0
    @9
    vz
    vy
    @0
    @7
    @8
    @0
    @7
    @3
    cA
    wss
    #
    @8
    @0
    @0
    @7
    @3
    cA
    wcel
    #
    @11
    @0
    idn1
    @0
    @7
    @4
    cA
    wss
    #
    @5
    @12
    @0
    @7
    @6
    @13
    @0
    @7
    @7
    @6
    @0
    @7
    idn2
    #
    @5
    @6
    simpr
    e2
    @4
    cA
    elpwi
    e2
    @0
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
    cA
    @3
    trss
    e12
    @3
    cA
    vz
    vex
    elpw
    e2bir
    in2
    gen12
    @2
    @10
    biimpr
    e01
    in1
end
