include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "sspwuni.mm"
include "biimpi.mm"
include "intssuni.mm"
include "sstr.mm"
include "expcom.mm"
include "syl2im.mm"

theorem bj-intss
  let cA: class A
  let cX: class X


  assert |- ( A C_ ~P X -> ( A =/= (/) -> |^| A C_ X ) )

  proof
    cA
    cX
    cpw
    wss
    #
    cA
    cuni
    #
    cX
    wss
    #
    cA
    c0
    wne
    cA
    cint
    #
    @1
    wss
    #
    @3
    cX
    wss
    #
    @0
    @2
    cA
    cX
    sspwuni
    biimpi
    cA
    intssuni
    @4
    @2
    @5
    @3
    @1
    cX
    sstr
    expcom
    syl2im
end
