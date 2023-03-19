include "wcel.mm"
include "csn.mm"
include "cpw.mm"
include "cvv.mm"
include "wss.mm"
include "snex.mm"
include "idn1.mm"
include "snssi.mm"
include "e1a.mm"
include "elpwg.mm"
include "biimprd.mm"
include "e01.mm"
include "in1.mm"

theorem snelpwrVD
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> { A } e. ~P B )

  proof
    cA
    cB
    wcel
    #
    cA
    csn
    #
    cB
    cpw
    wcel
    #
    @1
    cvv
    wcel
    #
    @0
    @1
    cB
    wss
    #
    @2
    cA
    snex
    @0
    @0
    @4
    @0
    idn1
    cA
    cB
    snssi
    e1a
    @3
    @2
    @4
    @1
    cB
    cvv
    elpwg
    biimprd
    e01
    in1
end
