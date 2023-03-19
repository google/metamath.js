include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "fac0.mm"
include "1nn.mm"
include "eqeltri.mm"
include "cn0.mm"
include "wa.mm"
include "cmul.mm"
include "facp1.mm"
include "adantl.mm"
include "nn0p1nn.mm"
include "nnmulcl.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "expcom.mm"
include "nn0ind.mm"

theorem faccl
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( N e. NN0 -> ( ! ` N ) e. NN )

  proof
    vj
    cv
    #
    cfa
    cfv
    #
    cn
    wcel
    cc0
    cfa
    cfv
    #
    cn
    wcel
    vk
    cv
    #
    cfa
    cfv
    #
    cn
    wcel
    #
    @3
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cn
    wcel
    #
    cN
    cfa
    cfv
    #
    cn
    wcel
    vj
    vk
    cN
    @0
    cc0
    wceq
    @1
    @2
    cn
    @0
    cc0
    cfa
    fveq2
    eleq1d
    @0
    @3
    wceq
    @1
    @4
    cn
    @0
    @3
    cfa
    fveq2
    eleq1d
    @0
    @6
    wceq
    @1
    @7
    cn
    @0
    @6
    cfa
    fveq2
    eleq1d
    @0
    cN
    wceq
    @1
    @9
    cn
    @0
    cN
    cfa
    fveq2
    eleq1d
    @2
    c1
    cn
    fac0
    1nn
    eqeltri
    @5
    @3
    cn0
    wcel
    #
    @8
    @5
    @10
    wa
    @7
    @4
    @6
    cmul
    co
    #
    cn
    @10
    @7
    @11
    wceq
    @5
    @3
    facp1
    adantl
    @10
    @5
    @6
    cn
    wcel
    @11
    cn
    wcel
    @3
    nn0p1nn
    @4
    @6
    nnmulcl
    sylan2
    eqeltrd
    expcom
    nn0ind
end
