include "cv.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "cq.mm"
include "c1.mm"
include "zcn.mm"
include "div1d.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6rbbr.mm"
include "1nn.mm"
include "oveq2.mm"
include "rspcev.mm"
include "mpan.mm"
include "syl6bi.mm"
include "reximia.mm"
include "risset.mm"
include "elq.mm"
include "3imtr4i.mm"

theorem zq
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ZZ -> A e. QQ )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vx
    cz
    wrex
    cA
    @0
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    #
    vx
    cz
    wrex
    cA
    cz
    wcel
    cA
    cq
    wcel
    @1
    @5
    vx
    cz
    @0
    cz
    wcel
    #
    @1
    cA
    @0
    c1
    cdiv
    co
    #
    wceq
    #
    @5
    @6
    @8
    cA
    @0
    wceq
    @1
    @6
    @7
    @0
    cA
    @6
    @0
    @0
    zcn
    div1d
    eqeq2d
    @0
    cA
    eqcom
    syl6rbbr
    c1
    cn
    wcel
    @8
    @5
    1nn
    @4
    @8
    vy
    c1
    cn
    @2
    c1
    wceq
    @3
    @7
    cA
    @2
    c1
    @0
    cdiv
    oveq2
    eqeq2d
    rspcev
    mpan
    syl6bi
    reximia
    vx
    cA
    cz
    risset
    vx
    vy
    cA
    elq
    3imtr4i
end
