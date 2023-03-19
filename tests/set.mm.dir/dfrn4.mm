include "cvv.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "rnresv.mm"
include "eqtr2i.mm"

theorem dfrn4
  let cA: class A


  assert |- ran A = ( A " _V )

  proof
    cA
    cvv
    cima
    cA
    cvv
    cres
    crn
    cA
    crn
    cA
    cvv
    df-ima
    cA
    rnresv
    eqtr2i
end
