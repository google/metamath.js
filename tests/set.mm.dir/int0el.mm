include "c0.mm"
include "wcel.mm"
include "cint.mm"
include "intss1.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "eqssd.mm"

theorem int0el
  let cA: class A


  assert |- ( (/) e. A -> |^| A = (/) )

  proof
    c0
    cA
    wcel
    #
    cA
    cint
    #
    c0
    c0
    cA
    intss1
    c0
    @1
    wss
    @0
    @1
    0ss
    a1i
    eqssd
end
