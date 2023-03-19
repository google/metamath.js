include "wdfat.mm"
include "wn.mm"
include "cafv.mm"
include "cfv.mm"
include "cvv.mm"
include "cif.mm"
include "dfafv2.mm"
include "iffalse.mm"
include "syl5eq.mm"

theorem afvnfundmuv
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. F defAt A -> ( F ''' A ) = _V )

  proof
    cA
    cF
    wdfat
    #
    wn
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
    cvv
    cA
    cF
    dfafv2
    @0
    @1
    cvv
    iffalse
    syl5eq
end
