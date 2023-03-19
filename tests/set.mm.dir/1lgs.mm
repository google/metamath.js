include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "clgs.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "sq1.mm"
include "oveq1i.mm"
include "cgcd.mm"
include "wceq.mm"
include "1gcd.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "1z.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "lgssq.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "syl5eqr.mm"

theorem 1lgs
  let cN: class N


  assert |- ( N e. ZZ -> ( 1 /L N ) = 1 )

  proof
    cN
    cz
    wcel
    #
    c1
    cN
    clgs
    co
    c1
    c2
    cexp
    co
    #
    cN
    clgs
    co
    #
    c1
    @1
    c1
    cN
    clgs
    sq1
    oveq1i
    @0
    c1
    cN
    cgcd
    co
    c1
    wceq
    #
    @2
    c1
    wceq
    #
    cN
    1gcd
    c1
    cz
    wcel
    #
    c1
    cc0
    wne
    #
    wa
    @0
    @3
    @4
    @5
    @6
    1z
    ax-1ne0
    pm3.2i
    c1
    cN
    lgssq
    mp3an1
    mpdan
    syl5eqr
end
