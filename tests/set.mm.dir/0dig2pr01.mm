include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "c2.mm"
include "cdig.mm"
include "cfv.mm"
include "co.mm"
include "elpri.mm"
include "cn.mm"
include "cz.mm"
include "2nn.mm"
include "0z.mm"
include "dig0.mm"
include "mp2an.mm"
include "oveq2.mm"
include "id.mm"
include "3eqtr4a.mm"
include "cuz.mm"
include "2z.mm"
include "uzid.mm"
include "0dig1.mm"
include "mp2b.mm"
include "jaoi.mm"
include "syl.mm"

theorem 0dig2pr01
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. { 0 , 1 } -> ( 0 ( digit ` 2 ) N ) = N )

  proof
    cN
    cc0
    c1
    cpr
    wcel
    cN
    cc0
    wceq
    #
    cN
    c1
    wceq
    #
    wo
    cc0
    cN
    c2
    cdig
    cfv
    #
    co
    #
    cN
    wceq
    #
    cN
    cc0
    c1
    elpri
    @0
    @4
    @1
    @0
    cc0
    cc0
    @2
    co
    #
    cc0
    @3
    cN
    c2
    cn
    wcel
    cc0
    cz
    wcel
    @5
    cc0
    wceq
    2nn
    0z
    c2
    cc0
    dig0
    mp2an
    cN
    cc0
    cc0
    @2
    oveq2
    @0
    id
    3eqtr4a
    @1
    cc0
    c1
    @2
    co
    #
    c1
    @3
    cN
    c2
    cz
    wcel
    c2
    c2
    cuz
    cfv
    wcel
    @6
    c1
    wceq
    2z
    c2
    uzid
    c2
    0dig1
    mp2b
    cN
    c1
    cc0
    @2
    oveq2
    @1
    id
    3eqtr4a
    jaoi
    syl
end
