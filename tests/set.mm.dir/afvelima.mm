include "wfun.mm"
include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "cafv.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "elimag.mm"
include "ibi.mm"
include "funbrafv.mm"
include "reximdv.mm"
include "syl5.mm"
include "imp.mm"

theorem afvelima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint k x
  assert |- ( ( Fun F /\ A e. ( F " B ) ) -> E. x e. B ( F ''' x ) = A )

  proof
    cF
    wfun
    #
    cA
    cF
    cB
    cima
    #
    wcel
    #
    vx
    cv
    #
    cF
    cafv
    cA
    wceq
    #
    vx
    cB
    wrex
    #
    @2
    @3
    cA
    cF
    wbr
    #
    vx
    cB
    wrex
    #
    @0
    @5
    @2
    @7
    vx
    cA
    cF
    cB
    @1
    elimag
    ibi
    @0
    @6
    @4
    vx
    cB
    @3
    cA
    cF
    funbrafv
    reximdv
    syl5
    imp
end
