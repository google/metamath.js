include "cvv.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "numth3.mm"
include "fodomnum.mm"
include "mp2b.mm"

theorem fodom
  let cA: class A
  let cB: class B
  let cF: class F
  assume fodom.1: |- A e. _V


  assert |- ( F : A -onto-> B -> B ~<_ A )

  proof
    cA
    cvv
    wcel
    cA
    ccrd
    cdm
    wcel
    cA
    cB
    cF
    wfo
    cB
    cA
    cdom
    wbr
    wi
    fodom.1
    cA
    cvv
    numth3
    cA
    cB
    cF
    fodomnum
    mp2b
end
