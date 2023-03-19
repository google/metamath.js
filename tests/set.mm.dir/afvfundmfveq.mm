include "wdfat.mm"
include "cafv.mm"
include "cfv.mm"
include "cvv.mm"
include "cif.mm"
include "dfafv2.mm"
include "iftrue.mm"
include "syl5eq.mm"

theorem afvfundmfveq
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( F defAt A -> ( F ''' A ) = ( F ` A ) )

  proof
    cA
    cF
    wdfat
    #
    cA
    cF
    cafv
    @0
    cA
    cF
    cfv
    #
    cvv
    cif
    @1
    cA
    cF
    dfafv2
    @0
    @1
    cvv
    iftrue
    syl5eq
end
