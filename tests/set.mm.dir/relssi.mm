include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wrel.mm"
include "wb.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "ax-gen.mm"
include "mpgbir.mm"

theorem relssi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume relssi.1: |- Rel A
  assume relssi.2: |- ( <. x , y >. e. A -> <. x , y >. e. B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- A C_ B

  proof
    cA
    cB
    wss
    #
    vx
    cv
    vy
    cv
    cop
    #
    cA
    wcel
    @1
    cB
    wcel
    wi
    #
    vy
    wal
    #
    vx
    cA
    wrel
    @0
    @3
    vx
    wal
    wb
    relssi.1
    vx
    vy
    cA
    cB
    ssrel
    ax-mp
    @2
    vy
    relssi.2
    ax-gen
    mpgbir
end
