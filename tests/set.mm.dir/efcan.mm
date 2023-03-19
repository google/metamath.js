include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cmul.mm"
include "c1.mm"
include "wceq.mm"
include "negcl.mm"
include "efadd.mm"
include "mpdan.mm"
include "cc0.mm"
include "negid.mm"
include "fveq2d.mm"
include "ef0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem efcan
  let cA: class A


  assert |- ( A e. CC -> ( ( exp ` A ) x. ( exp ` -u A ) ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cA
    cneg
    #
    caddc
    co
    #
    ce
    cfv
    #
    cA
    ce
    cfv
    @1
    ce
    cfv
    cmul
    co
    #
    c1
    @0
    @1
    cc
    wcel
    @3
    @4
    wceq
    cA
    negcl
    cA
    @1
    efadd
    mpdan
    @0
    @3
    cc0
    ce
    cfv
    c1
    @0
    @2
    cc0
    ce
    cA
    negid
    fveq2d
    ef0
    syl6eq
    eqtr3d
end
