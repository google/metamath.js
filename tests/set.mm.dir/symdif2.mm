include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wn.mm"
include "cdif.mm"
include "cun.mm"
include "wo.mm"
include "wa.mm"
include "eldif.mm"
include "orbi12i.mm"
include "elun.mm"
include "xor.mm"
include "3bitr4i.mm"
include "abbi2i.mm"

theorem symdif2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A \ B ) u. ( B \ A ) ) = { x | -. ( x e. A <-> x e. B ) }

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wb
    wn
    #
    vx
    cA
    cB
    cdif
    #
    cB
    cA
    cdif
    #
    cun
    #
    @0
    @4
    wcel
    #
    @0
    @5
    wcel
    #
    wo
    @1
    @2
    wn
    wa
    #
    @2
    @1
    wn
    wa
    #
    wo
    @0
    @6
    wcel
    @3
    @7
    @9
    @8
    @10
    @0
    cA
    cB
    eldif
    @0
    cB
    cA
    eldif
    orbi12i
    @0
    @4
    @5
    elun
    @1
    @2
    xor
    3bitr4i
    abbi2i
end
