include "c1.mm"
include "cdc.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "dfdec10.mm"
include "ax-1cn.mm"
include "10nn.mm"
include "nncni.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "exp1.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "mulcomli.mm"
include "oveq1i.mm"
include "eqtri.mm"

theorem 1t10e1p1e11
  let vk: setvar k
  let vx: setvar x


  assert |- ; 1 1 = ( ( 1 x. ( ; 1 0 ^ 1 ) ) + 1 )

  proof
    c1
    c1
    cdc
    c1
    cc0
    cdc
    #
    c1
    cmul
    co
    #
    c1
    caddc
    co
    c1
    @0
    c1
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    c1
    c1
    dfdec10
    @1
    @3
    c1
    caddc
    c1
    @0
    @3
    ax-1cn
    @0
    10nn
    nncni
    #
    @0
    @2
    c1
    cmul
    @2
    @0
    @0
    cc
    wcel
    @2
    @0
    wceq
    @4
    @0
    exp1
    ax-mp
    eqcomi
    oveq2i
    mulcomli
    oveq1i
    eqtri
end
