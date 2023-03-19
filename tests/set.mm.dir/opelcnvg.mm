include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "wbr.mm"
include "cop.mm"
include "cv.mm"
include "breq2.mm"
include "breq1.mm"
include "df-cnv.mm"
include "brabg.mm"
include "df-br.mm"
include "3bitr3g.mm"

theorem opelcnvg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. `' R <-> <. B , A >. e. R ) )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cA
    cB
    cR
    ccnv
    #
    wbr
    cB
    cA
    cR
    wbr
    #
    cA
    cB
    cop
    @0
    wcel
    cB
    cA
    cop
    cR
    wcel
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    @2
    cA
    cR
    wbr
    @1
    vx
    vy
    cA
    cB
    cC
    cD
    @0
    @3
    cA
    @2
    cR
    breq2
    @2
    cB
    cA
    cR
    breq1
    vx
    vy
    cR
    df-cnv
    brabg
    cA
    cB
    @0
    df-br
    cB
    cA
    cR
    df-br
    3bitr3g
end
