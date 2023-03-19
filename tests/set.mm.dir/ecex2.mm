include "cres.mm"
include "wcel.mm"
include "cec.mm"
include "cvv.mm"
include "ecexg.mm"
include "ecres2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"

theorem ecex2
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V


  assert |- ( ( R |` A ) e. V -> ( B e. A -> [ B ] R e. _V ) )

  proof
    cR
    cA
    cres
    #
    cV
    wcel
    cB
    @0
    cec
    #
    cvv
    wcel
    cB
    cA
    wcel
    #
    cB
    cR
    cec
    #
    cvv
    wcel
    cB
    cV
    @0
    ecexg
    @2
    @1
    @3
    cvv
    cA
    cB
    cR
    ecres2
    eleq1d
    syl5ibcom
end
