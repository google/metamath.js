include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfin7.mm"
include "cfn.mm"
include "wi.mm"
include "isfin7-2.mm"
include "biimt.mm"
include "bitr4d.mm"

theorem fin71num
  let cA: class A


  assert |- ( A e. dom card -> ( A e. Fin7 <-> A e. Fin ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    cfin7
    wcel
    @1
    cA
    cfn
    wcel
    #
    wi
    @2
    cA
    @0
    isfin7-2
    @1
    @2
    biimt
    bitr4d
end
