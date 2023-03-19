include "cvv.mm"
include "wcel.mm"
include "cafv.mm"
include "wn.mm"
include "wceq.mm"
include "afvprc.mm"
include "nvelim.mm"
include "syl.mm"
include "con4i.mm"

theorem afvvv
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) e. B -> A e. _V )

  proof
    cA
    cvv
    wcel
    #
    cA
    cF
    cafv
    #
    cB
    wcel
    #
    @0
    wn
    @1
    cvv
    wceq
    @2
    wn
    cA
    cF
    afvprc
    @1
    cB
    nvelim
    syl
    con4i
end
