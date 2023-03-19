include "c2.mm"
include "c6.mm"
include "cmul.mm"
include "co.mm"
include "c3.mm"
include "c4.mm"
include "cmin.mm"
include "caddc.mm"
include "cc0.mm"
include "6cn.mm"
include "2timesi.mm"
include "2p2e4.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "3cn.mm"
include "2cn.mm"
include "adddii.mm"
include "3t2e6.mm"
include "oveq12i.mm"
include "3eqtri.mm"
include "addcli.mm"
include "subidi.mm"
include "eqtri.mm"

theorem 2t6m3t4e0
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 2 x. 6 ) - ( 3 x. 4 ) ) = 0

  proof
    c2
    c6
    cmul
    co
    #
    c3
    c4
    cmul
    co
    #
    cmin
    co
    c6
    c6
    caddc
    co
    #
    @2
    cmin
    co
    cc0
    @0
    @2
    @1
    @2
    cmin
    c6
    6cn
    2timesi
    @1
    c3
    c2
    c2
    caddc
    co
    #
    cmul
    co
    c3
    c2
    cmul
    co
    #
    @4
    caddc
    co
    @2
    c4
    @3
    c3
    cmul
    @3
    c4
    2p2e4
    eqcomi
    oveq2i
    c3
    c2
    c2
    3cn
    2cn
    2cn
    adddii
    @4
    c6
    @4
    c6
    caddc
    3t2e6
    3t2e6
    oveq12i
    3eqtri
    oveq12i
    @2
    c6
    c6
    6cn
    6cn
    addcli
    subidi
    eqtri
end
