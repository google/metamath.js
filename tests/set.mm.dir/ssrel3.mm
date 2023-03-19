include "wrel.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wbr.mm"
include "ssrel.mm"
include "df-br.mm"
include "imbi12i.mm"
include "2albii.mm"
include "syl6bbr.mm"

theorem ssrel3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( Rel A -> ( A C_ B <-> A. x A. y ( x A y -> x B y ) ) )

  proof
    cA
    wrel
    cA
    cB
    wss
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    @0
    @1
    cA
    wbr
    #
    @0
    @1
    cB
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    vx
    vy
    cA
    cB
    ssrel
    @8
    @5
    vx
    vy
    @6
    @3
    @7
    @4
    @0
    @1
    cA
    df-br
    @0
    @1
    cB
    df-br
    imbi12i
    2albii
    syl6bbr
end
