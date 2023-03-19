include "cafv.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wn.mm"
include "wdfat.mm"
include "afvfundmfveq.mm"
include "con3i.mm"
include "afvnfundmuv.mm"
include "syl.mm"
include "necon1ai.mm"

theorem afvnufveq
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) =/= _V -> ( F ''' A ) = ( F ` A ) )

  proof
    cA
    cF
    cafv
    #
    cA
    cF
    cfv
    wceq
    #
    @0
    cvv
    @1
    wn
    cA
    cF
    wdfat
    #
    wn
    @0
    cvv
    wceq
    @2
    @1
    cA
    cF
    afvfundmfveq
    con3i
    cA
    cF
    afvnfundmuv
    syl
    necon1ai
end
