include "wcel.mm"
include "cec.mm"
include "csn.mm"
include "cima.mm"
include "cvv.mm"
include "df-ec.mm"
include "imaexg.mm"
include "syl5eqel.mm"

theorem ecexg
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( R e. B -> [ A ] R e. _V )

  proof
    cR
    cB
    wcel
    cA
    cR
    cec
    cR
    cA
    csn
    #
    cima
    cvv
    cA
    cR
    df-ec
    cR
    @0
    cB
    imaexg
    syl5eqel
end
