include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "ax-gen.mm"
include "wnfc.mm"
include "wb.mm"
include "csbiebt.mm"
include "mpdan.mm"
include "mpbii.mm"

theorem csbiegf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume csbiegf.1: |- ( A e. V -> F/_ x C )
  assume csbiegf.2: |- ( x = A -> B = C )

  disjoint A x
  disjoint V x
  assert |- ( A e. V -> [_ A / x ]_ B = C )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    cA
    wceq
    cB
    cC
    wceq
    wi
    #
    vx
    wal
    #
    vx
    cA
    cB
    csb
    cC
    wceq
    #
    @1
    vx
    csbiegf.2
    ax-gen
    @0
    vx
    cC
    wnfc
    @2
    @3
    wb
    csbiegf.1
    vx
    cA
    cB
    cC
    cV
    csbiebt
    mpdan
    mpbii
end
