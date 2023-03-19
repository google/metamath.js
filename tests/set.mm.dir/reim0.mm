include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cim.mm"
include "cfv.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "it0e0.mm"
include "oveq2i.mm"
include "addid1.mm"
include "syl5eq.mm"
include "syl.mm"
include "fveq2d.mm"
include "0re.mm"
include "crim.mm"
include "mpan2.mm"
include "eqtr3d.mm"

theorem reim0
  let cA: class A


  assert |- ( A e. RR -> ( Im ` A ) = 0 )

  proof
    cA
    cr
    wcel
    #
    cA
    ci
    cc0
    cmul
    co
    #
    caddc
    co
    #
    cim
    cfv
    #
    cA
    cim
    cfv
    cc0
    @0
    @2
    cA
    cim
    @0
    cA
    cc
    wcel
    #
    @2
    cA
    wceq
    cA
    recn
    @4
    @2
    cA
    cc0
    caddc
    co
    cA
    @1
    cc0
    cA
    caddc
    it0e0
    oveq2i
    cA
    addid1
    syl5eq
    syl
    fveq2d
    @0
    cc0
    cr
    wcel
    @3
    cc0
    wceq
    0re
    cA
    cc0
    crim
    mpan2
    eqtr3d
end
