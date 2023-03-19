include "wcel.mm"
include "wf1o.mm"
include "cvv.mm"
include "cen.mm"
include "wbr.mm"
include "wfo.mm"
include "f1ofo.mm"
include "fornex.mm"
include "syl5.mm"
include "imp.mm"
include "f1oen2g.mm"
include "3com23.mm"
include "mpd3an3.mm"

theorem f1oeng
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f


  assert |- ( ( A e. C /\ F : A -1-1-onto-> B ) -> A ~~ B )

  proof
    cA
    cC
    wcel
    #
    cA
    cB
    cF
    wf1o
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    cen
    wbr
    #
    @0
    @1
    @2
    @1
    cA
    cB
    cF
    wfo
    @0
    @2
    cA
    cB
    cF
    f1ofo
    cA
    cB
    cC
    cF
    fornex
    syl5
    imp
    @0
    @2
    @1
    @3
    cA
    cB
    cF
    cC
    cvv
    f1oen2g
    3com23
    mpd3an3
end
