include "wcel.mm"
include "cfv.mm"
include "ffvelrni.mm"
include "cdm.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "syl6eqel.mm"
include "sylnbir.mm"
include "pm2.61i.mm"

theorem f0cli
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume f0cl.1: |- F : A --> B
  assume f0cl.2: |- (/) e. B


  assert |- ( F ` C ) e. B

  proof
    cC
    cA
    wcel
    #
    cC
    cF
    cfv
    #
    cB
    wcel
    #
    cA
    cB
    cC
    cF
    f0cl.1
    ffvelrni
    @0
    cC
    cF
    cdm
    #
    wcel
    #
    @2
    @3
    cA
    cC
    cA
    cB
    cF
    f0cl.1
    fdmi
    eleq2i
    @4
    wn
    @1
    c0
    cB
    cC
    cF
    ndmfv
    f0cl.2
    syl6eqel
    sylnbir
    pm2.61i
end
