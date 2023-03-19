include "wfun.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccnv.mm"
include "cint.mm"
include "cima.mm"
include "cv.mm"
include "ciin.mm"
include "intiin.mm"
include "imaeq2i.mm"
include "iinpreima.mm"
include "syl5eq.mm"

theorem intpreima
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  assert |- ( ( Fun F /\ A =/= (/) ) -> ( `' F " |^| A ) = |^|_ x e. A ( `' F " x ) )

  proof
    cF
    wfun
    cA
    c0
    wne
    wa
    cF
    ccnv
    #
    cA
    cint
    #
    cima
    @0
    vx
    cA
    vx
    cv
    #
    ciin
    #
    cima
    vx
    cA
    @0
    @2
    cima
    ciin
    @1
    @3
    @0
    vx
    cA
    intiin
    imaeq2i
    vx
    cA
    @2
    cF
    iinpreima
    syl5eq
end
