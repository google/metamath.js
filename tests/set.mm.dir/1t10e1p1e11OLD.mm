include "c1.mm"
include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "dfdecOLD.mm"
include "ax-1cn.mm"
include "10nnOLD.mm"
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

theorem 1t10e1p1e11OLD
  let vk: setvar k
  let vx: setvar x


  assert |- ; 1 1 = ( ( 1 x. ( 10 ^ 1 ) ) + 1 )

  proof
    c1
    c1
    cdc
    c10
    c1
    cmul
    co
    #
    c1
    caddc
    co
    c1
    c10
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
    dfdecOLD
    @0
    @2
    c1
    caddc
    c1
    c10
    @2
    ax-1cn
    c10
    10nnOLD
    nncni
    #
    c10
    @1
    c1
    cmul
    @1
    c10
    c10
    cc
    wcel
    @1
    c10
    wceq
    @3
    c10
    exp1
    ax-mp
    eqcomi
    oveq2i
    mulcomli
    oveq1i
    eqtri
end
