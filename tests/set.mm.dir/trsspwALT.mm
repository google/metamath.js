include "wtr.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "dfss2.mm"
include "idn1.mm"
include "idn2.mm"
include "trss.mm"
include "e12.mm"
include "vex.mm"
include "elpw.mm"
include "e2bir.mm"
include "in2.mm"
include "gen11.mm"
include "biimpr.mm"
include "e01.mm"
include "in1.mm"

theorem trsspwALT
  let cA: class A
  let vx: setvar x


  assert |- ( Tr A -> A C_ ~P A )

  proof
    cA
    wtr
    #
    cA
    cA
    cpw
    #
    wss
    #
    @2
    vx
    cv
    #
    cA
    wcel
    #
    @3
    @1
    wcel
    #
    wi
    #
    vx
    wal
    #
    wb
    @0
    @7
    @2
    vx
    cA
    @1
    dfss2
    @0
    @6
    vx
    @0
    @4
    @5
    @0
    @4
    @3
    cA
    wss
    #
    @5
    @0
    @0
    @4
    @4
    @8
    @0
    idn1
    @0
    @4
    idn2
    cA
    @3
    trss
    e12
    @3
    cA
    vx
    vex
    elpw
    e2bir
    in2
    gen11
    @2
    @7
    biimpr
    e01
    in1
end
