include "cn.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "c2.mm"
include "cabs.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "nnne0.mm"
include "blenn0.mm"
include "mpdan.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem blennn
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( #b ` N ) = ( ( |_ ` ( 2 logb N ) ) + 1 ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cblen
    cfv
    #
    c2
    cN
    cabs
    cfv
    #
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    @0
    cN
    cc0
    wne
    @1
    @5
    wceq
    cN
    nnne0
    cN
    cn
    blenn0
    mpdan
    @0
    @4
    @7
    c1
    caddc
    @0
    @3
    @6
    cfl
    @0
    @2
    cN
    c2
    clogb
    @0
    cN
    cN
    nnre
    @0
    cN
    cN
    nnnn0
    nn0ge0d
    absidd
    oveq2d
    fveq2d
    oveq1d
    eqtrd
end
