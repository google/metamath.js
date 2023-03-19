include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "19.8a.mm"
include "ex.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "eqvisset.mm"
include "alexeqg.mm"
include "syl.mm"
include "sp.mm"
include "com12.mm"
include "sylbird.mm"
include "impbid.mm"

theorem ceqex
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( x = A -> ( ph <-> E. x ( x = A /\ ph ) ) )

  proof
    vx
    cv
    cA
    wceq
    #
    wph
    @0
    wph
    wa
    #
    vx
    wex
    #
    @0
    wph
    @2
    @1
    vx
    19.8a
    ex
    @0
    @2
    @0
    wph
    wi
    #
    vx
    wal
    #
    wph
    @0
    cA
    cvv
    wcel
    @4
    @2
    wb
    vx
    cA
    eqvisset
    wph
    vx
    cA
    cvv
    alexeqg
    syl
    @4
    @0
    wph
    @3
    vx
    sp
    com12
    sylbird
    impbid
end
