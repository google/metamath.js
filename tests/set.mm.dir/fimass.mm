include "wf.mm"
include "cima.mm"
include "crn.mm"
include "wss.mm"
include "imassrn.mm"
include "a1i.mm"
include "frn.mm"
include "sstrd.mm"

theorem fimass
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X


  assert |- ( F : A --> B -> ( F " X ) C_ B )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cX
    cima
    #
    cF
    crn
    #
    cB
    @1
    @2
    wss
    @0
    cF
    cX
    imassrn
    a1i
    cA
    cB
    cF
    frn
    sstrd
end
