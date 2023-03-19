include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "spsbc.mm"
include "sbcimg.mm"
include "wb.mm"
include "eqid.mm"
include "eqsbc3.mm"
include "mpbiri.mm"
include "pm5.5.mm"
include "syl.mm"
include "3bitrd.mm"
include "sylibd.mm"

theorem sbceqal
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint B x
  disjoint A x
  assert |- ( A e. V -> ( A. x ( x = A -> x = B ) -> A = B ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wi
    #
    vx
    wal
    @4
    vx
    cA
    wsbc
    #
    cA
    cB
    wceq
    #
    @4
    vx
    cA
    cV
    spsbc
    @0
    @5
    @2
    vx
    cA
    wsbc
    #
    @3
    vx
    cA
    wsbc
    #
    wi
    #
    @8
    @6
    @2
    @3
    vx
    cA
    cV
    sbcimg
    @0
    @7
    @9
    @8
    wb
    @0
    @7
    cA
    cA
    wceq
    cA
    eqid
    vx
    cA
    cA
    cV
    eqsbc3
    mpbiri
    @7
    @8
    pm5.5
    syl
    vx
    cA
    cB
    cV
    eqsbc3
    3bitrd
    sylibd
end
