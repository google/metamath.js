include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "imaeq1.mm"
include "eleq2.mm"
include "alrimiv.mm"
include "syl.mm"
include "abbi.mm"
include "sylib.mm"

theorem bj-cleq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A = B -> { x | { x } e. ( A " C ) } = { x | { x } e. ( B " C ) } )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    csn
    #
    cA
    cC
    cima
    #
    wcel
    #
    @1
    cB
    cC
    cima
    #
    wcel
    #
    wb
    #
    vx
    wal
    #
    @3
    vx
    cab
    @5
    vx
    cab
    wceq
    @0
    @2
    @4
    wceq
    #
    @7
    cA
    cB
    cC
    imaeq1
    @8
    @6
    vx
    @2
    @4
    @1
    eleq2
    alrimiv
    syl
    @3
    @5
    vx
    abbi
    sylib
end
