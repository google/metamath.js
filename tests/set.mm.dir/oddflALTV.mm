include "codd.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "zofldiv2ALTV.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cz.mm"
include "cc.mm"
include "oddz.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "syl.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "wceq.mm"
include "npcan1.mm"
include "3eqtrrd.mm"

theorem oddflALTV
  let cK: class K
  let vk: setvar k
  let vx: setvar x


  assert |- ( K e. Odd -> K = ( ( 2 x. ( |_ ` ( K / 2 ) ) ) + 1 ) )

  proof
    cK
    codd
    wcel
    #
    c2
    cK
    c2
    cdiv
    co
    cfl
    cfv
    #
    cmul
    co
    #
    c1
    caddc
    co
    c2
    cK
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    @3
    c1
    caddc
    co
    #
    cK
    @0
    @2
    @5
    c1
    caddc
    @0
    @1
    @4
    c2
    cmul
    cK
    zofldiv2ALTV
    oveq2d
    oveq1d
    @0
    @5
    @3
    c1
    caddc
    @0
    @3
    c2
    @0
    cK
    cz
    wcel
    #
    @3
    cc
    wcel
    cK
    oddz
    #
    @7
    @3
    cK
    peano2zm
    zcnd
    syl
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan2d
    oveq1d
    @0
    cK
    cc
    wcel
    @6
    cK
    wceq
    @0
    cK
    @8
    zcnd
    cK
    npcan1
    syl
    3eqtrrd
end
