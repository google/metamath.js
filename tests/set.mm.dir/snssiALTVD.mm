include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "dfss2.mm"
include "wceq.mm"
include "idn1.mm"
include "idn2.mm"
include "velsn.mm"
include "e2bi.mm"
include "eleq1a.mm"
include "e12.mm"
include "in2.mm"
include "gen11.mm"
include "biimpr.mm"
include "e01.mm"
include "in1.mm"

theorem snssiALTVD
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A e. B -> { A } C_ B )

  proof
    cA
    cB
    wcel
    #
    cA
    csn
    #
    cB
    wss
    #
    @2
    vx
    cv
    #
    @1
    wcel
    #
    @3
    cB
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
    @1
    cB
    dfss2
    @0
    @6
    vx
    @0
    @4
    @5
    @0
    @0
    @4
    @3
    cA
    wceq
    #
    @5
    @0
    idn1
    @0
    @4
    @4
    @8
    @0
    @4
    idn2
    vx
    cA
    velsn
    e2bi
    cA
    cB
    @3
    eleq1a
    e12
    in2
    gen11
    @2
    @7
    biimpr
    e01
    in1
end
