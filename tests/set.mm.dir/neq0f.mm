include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "wex.mm"
include "eq0f.mm"
include "notbii.mm"
include "df-ex.mm"
include "bitr4i.mm"

theorem neq0f
  let vx: setvar x
  let cA: class A
  assume eq0f.1: |- F/_ x A


  assert |- ( -. A = (/) <-> E. x x e. A )

  proof
    cA
    c0
    wceq
    #
    wn
    vx
    cv
    cA
    wcel
    #
    wn
    vx
    wal
    #
    wn
    @1
    vx
    wex
    @0
    @2
    vx
    cA
    eq0f.1
    eq0f
    notbii
    @1
    vx
    df-ex
    bitr4i
end
