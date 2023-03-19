include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "wex.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "elin.mm"
include "exbii.mm"
include "nfin.mm"
include "n0f.mm"
include "df-rex.mm"
include "3bitr4i.mm"

theorem inn0f
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume inn0f.1: |- F/_ x A
  assume inn0f.2: |- F/_ x B


  assert |- ( ( A i^i B ) =/= (/) <-> E. x e. A x e. B )

  proof
    vx
    cv
    #
    cA
    cB
    cin
    #
    wcel
    #
    vx
    wex
    @0
    cA
    wcel
    @0
    cB
    wcel
    #
    wa
    #
    vx
    wex
    @1
    c0
    wne
    @3
    vx
    cA
    wrex
    @2
    @4
    vx
    @0
    cA
    cB
    elin
    exbii
    vx
    @1
    vx
    cA
    cB
    inn0f.1
    inn0f.2
    nfin
    n0f
    @3
    vx
    cA
    df-rex
    3bitr4i
end
