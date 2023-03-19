include "cop.mm"
include "wcel.mm"
include "wfun.mm"
include "wbr.mm"
include "cv.mm"
include "weu.mm"
include "df-br.mm"
include "wa.mm"
include "funeu.mm"
include "eubii.mm"
include "sylib.mm"
include "sylan2br.mm"

theorem funeu2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A y
  disjoint F y
  assert |- ( ( Fun F /\ <. A , B >. e. F ) -> E! y <. A , y >. e. F )

  proof
    cA
    cB
    cop
    cF
    wcel
    cF
    wfun
    #
    cA
    cB
    cF
    wbr
    #
    cA
    vy
    cv
    #
    cop
    cF
    wcel
    #
    vy
    weu
    #
    cA
    cB
    cF
    df-br
    @0
    @1
    wa
    cA
    @2
    cF
    wbr
    #
    vy
    weu
    @4
    vy
    cA
    cB
    cF
    funeu
    @5
    @3
    vy
    cA
    @2
    cF
    df-br
    eubii
    sylib
    sylan2br
end
