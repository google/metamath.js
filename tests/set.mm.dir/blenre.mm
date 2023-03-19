include "crp.mm"
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
include "rpne0.mm"
include "blenn0.mm"
include "mpdan.mm"
include "rpre.mm"
include "rpge0.mm"
include "absidd.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem blenre
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. RR+ -> ( #b ` N ) = ( ( |_ ` ( 2 logb N ) ) + 1 ) )

  proof
    cN
    crp
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
    rpne0
    cN
    crp
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
    rpre
    cN
    rpge0
    absidd
    oveq2d
    fveq2d
    oveq1d
    eqtrd
end
