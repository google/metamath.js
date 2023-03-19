include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cop.mm"
include "fneu.mm"
include "df-br.mm"
include "eubii.mm"
include "sylib.mm"

theorem fneu2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint F y
  disjoint B y
  assert |- ( ( F Fn A /\ B e. A ) -> E! y <. B , y >. e. F )

  proof
    cF
    cA
    wfn
    cB
    cA
    wcel
    wa
    cB
    vy
    cv
    #
    cF
    wbr
    #
    vy
    weu
    cB
    @0
    cop
    cF
    wcel
    #
    vy
    weu
    vy
    cA
    cB
    cF
    fneu
    @1
    @2
    vy
    cB
    @0
    cF
    df-br
    eubii
    sylib
end
