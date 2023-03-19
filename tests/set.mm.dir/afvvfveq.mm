include "cafv.mm"
include "wcel.mm"
include "cvv.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "nvelim.mm"
include "necon2ai.mm"
include "afvnufveq.mm"
include "syl.mm"

theorem afvvfveq
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) e. B -> ( F ''' A ) = ( F ` A ) )

  proof
    cA
    cF
    cafv
    #
    cB
    wcel
    #
    @0
    cvv
    wne
    @0
    cA
    cF
    cfv
    wceq
    @1
    @0
    cvv
    @0
    cB
    nvelim
    necon2ai
    cA
    cF
    afvnufveq
    syl
end
