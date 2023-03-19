include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "nncn.mm"
include "caddc.mm"
include "wa.mm"
include "npcan1.mm"
include "eleq1d.mm"
include "peano2cnm.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "elnn0nn.mm"
include "syl6bbr.mm"
include "biadan2.mm"

theorem elnnnn0
  let cN: class N


  assert |- ( N e. NN <-> ( N e. CC /\ ( N - 1 ) e. NN0 ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cc
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cn0
    wcel
    #
    cN
    nncn
    @1
    @0
    @2
    cc
    wcel
    #
    @2
    c1
    caddc
    co
    #
    cn
    wcel
    #
    wa
    #
    @3
    @1
    @6
    @0
    @7
    @1
    @5
    cN
    cn
    cN
    npcan1
    eleq1d
    @1
    @4
    @6
    cN
    peano2cnm
    biantrurd
    bitr3d
    @2
    elnn0nn
    syl6bbr
    biadan2
end
