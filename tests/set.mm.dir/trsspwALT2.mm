include "wtr.mm"
include "cpw.mm"
include "wss.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "wb.mm"
include "dfss2.mm"
include "id.mm"
include "idd.mm"
include "trss.mm"
include "sylsyld.mm"
include "vex.mm"
include "elpw.mm"
include "syl6ibr.mm"
include "idiALT.mm"
include "alrimiv.mm"
include "biimpr.mm"
include "mpsyl.mm"

theorem trsspwALT2
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
    wi
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
    @6
    wi
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
    id
    @0
    @4
    idd
    cA
    @3
    trss
    sylsyld
    @3
    cA
    vx
    vex
    elpw
    syl6ibr
    idiALT
    alrimiv
    @2
    @7
    biimpr
    mpsyl
    idiALT
end
