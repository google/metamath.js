include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wceq.mm"
include "velsn.mm"
include "eleq1a.mm"
include "syl5bi.mm"
include "alrimiv.mm"
include "dfss2.mm"
include "sylibr.mm"

theorem snssiALT
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A e. B -> { A } C_ B )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cA
    csn
    #
    wcel
    #
    @1
    cB
    wcel
    #
    wi
    #
    vx
    wal
    @2
    cB
    wss
    @0
    @5
    vx
    @3
    @1
    cA
    wceq
    @0
    @4
    vx
    cA
    velsn
    cA
    cB
    @1
    eleq1a
    syl5bi
    alrimiv
    vx
    @2
    cB
    dfss2
    sylibr
end
