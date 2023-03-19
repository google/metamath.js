include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cc0.mm"
include "cdc.mm"
include "c4.mm"
include "cmul.mm"
include "caddc.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "10nn.mm"
include "nncni.mm"
include "4cn.mm"
include "mulcli.mm"
include "pncan1.mm"
include "ax-mp.mm"
include "2cn.mm"
include "2ne0.mm"
include "divassi.mm"
include "4d2e2.mm"
include "oveq2i.mm"
include "2nn0.mm"
include "dec0u.mm"

theorem 41prothprmlem1
  let cP: class P
  let vk: setvar k
  let vx: setvar x
  assume 41prothprm.p: |- P = ; 4 1


  assert |- ( ( P - 1 ) / 2 ) = ; 2 0

  proof
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    c1
    cc0
    cdc
    #
    c4
    cmul
    co
    #
    c2
    cdiv
    co
    #
    c2
    cc0
    cdc
    #
    @0
    @2
    c2
    cdiv
    @0
    @2
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @2
    cP
    @5
    c1
    cmin
    cP
    c4
    c1
    cdc
    @5
    41prothprm.p
    c4
    c1
    dfdec10
    eqtri
    oveq1i
    @2
    cc
    wcel
    @6
    @2
    wceq
    @1
    c4
    @1
    10nn
    nncni
    #
    4cn
    mulcli
    @2
    pncan1
    ax-mp
    eqtri
    oveq1i
    @3
    @1
    c4
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @4
    @1
    c4
    c2
    @7
    4cn
    2cn
    2ne0
    divassi
    @9
    @1
    c2
    cmul
    co
    @4
    @8
    c2
    @1
    cmul
    4d2e2
    oveq2i
    c2
    2nn0
    dec0u
    eqtri
    eqtri
    eqtri
end
