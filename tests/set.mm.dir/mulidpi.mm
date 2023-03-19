include "cnpi.mm"
include "wcel.mm"
include "c1o.mm"
include "cmi.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "1pi.mm"
include "mulpiord.mm"
include "mpan2.mm"
include "com.mm"
include "pinn.mm"
include "nnm1.mm"
include "syl.mm"
include "eqtrd.mm"

theorem mulidpi
  let cA: class A


  assert |- ( A e. N. -> ( A .N 1o ) = A )

  proof
    cA
    cnpi
    wcel
    #
    cA
    c1o
    cmi
    co
    #
    cA
    c1o
    comu
    co
    #
    cA
    @0
    c1o
    cnpi
    wcel
    @1
    @2
    wceq
    1pi
    cA
    c1o
    mulpiord
    mpan2
    @0
    cA
    com
    wcel
    @2
    cA
    wceq
    cA
    pinn
    cA
    nnm1
    syl
    eqtrd
end
