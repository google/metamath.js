include "wf1.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "f1ores.mm"
include "f1oeng.mm"
include "ancoms.mm"
include "stoic3.mm"
include "ensymd.mm"

theorem f1imaeng
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V


  assert |- ( ( F : A -1-1-> B /\ C C_ A /\ C e. V ) -> ( F " C ) ~~ C )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cA
    wss
    #
    cC
    cV
    wcel
    #
    w3a
    cC
    cF
    cC
    cima
    #
    @0
    @1
    cC
    @3
    cF
    cC
    cres
    #
    wf1o
    #
    @2
    cC
    @3
    cen
    wbr
    #
    cA
    cB
    cC
    cF
    f1ores
    @2
    @5
    @6
    cC
    @3
    cV
    @4
    f1oeng
    ancoms
    stoic3
    ensymd
end
