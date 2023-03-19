include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "clgs.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "sq1.mm"
include "oveq2i.mm"
include "cgcd.mm"
include "wceq.mm"
include "gcd1.mm"
include "cn.mm"
include "1nn.mm"
include "lgssq2.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "syl5eqr.mm"

theorem lgs1
  let cA: class A


  assert |- ( A e. ZZ -> ( A /L 1 ) = 1 )

  proof
    cA
    cz
    wcel
    #
    cA
    c1
    clgs
    co
    cA
    c1
    c2
    cexp
    co
    #
    clgs
    co
    #
    c1
    @1
    c1
    cA
    clgs
    sq1
    oveq2i
    @0
    cA
    c1
    cgcd
    co
    c1
    wceq
    #
    @2
    c1
    wceq
    #
    cA
    gcd1
    @0
    c1
    cn
    wcel
    @3
    @4
    1nn
    cA
    c1
    lgssq2
    mp3an2
    mpdan
    syl5eqr
end
