include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "1cnd.mm"
include "binom2sub.mm"
include "mpdan.mm"
include "mulid1.mm"
include "oveq2d.mm"
include "sq1.mm"
include "a1i.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem binom2sub1
  let cA: class A


  assert |- ( A e. CC -> ( ( A - 1 ) ^ 2 ) = ( ( ( A ^ 2 ) - ( 2 x. A ) ) + 1 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    cmin
    co
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    c2
    cA
    c1
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    c2
    cexp
    co
    #
    caddc
    co
    #
    @2
    c2
    cA
    cmul
    co
    #
    cmin
    co
    #
    c1
    caddc
    co
    @0
    c1
    cc
    wcel
    @1
    @7
    wceq
    @0
    1cnd
    cA
    c1
    binom2sub
    mpdan
    @0
    @5
    @9
    @6
    c1
    caddc
    @0
    @4
    @8
    @2
    cmin
    @0
    @3
    cA
    c2
    cmul
    cA
    mulid1
    oveq2d
    oveq2d
    @6
    c1
    wceq
    @0
    sq1
    a1i
    oveq12d
    eqtrd
end
