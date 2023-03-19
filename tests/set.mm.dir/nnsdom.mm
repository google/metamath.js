include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "csdm.mm"
include "wbr.mm"
include "omex.mm"
include "nnsdomg.mm"
include "mpan.mm"

theorem nnsdom
  let cA: class A


  assert |- ( A e. _om -> A ~< _om )

  proof
    com
    cvv
    wcel
    cA
    com
    wcel
    cA
    com
    csdm
    wbr
    omex
    cA
    nnsdomg
    mpan
end
