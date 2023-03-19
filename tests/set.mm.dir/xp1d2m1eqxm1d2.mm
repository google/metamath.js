include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "peano2cn.mm"
include "halfcld.mm"
include "peano2cnm.mm"
include "syl.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "cmul.mm"
include "1cnd.mm"
include "subdird.mm"
include "divcan1d.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "wceq.mm"
include "2m1e1.mm"
include "oveq2d.mm"
include "id.mm"
include "subsub3d.mm"
include "3eqtr2rd.mm"
include "3eqtrd.mm"
include "mulcan2ad.mm"

theorem xp1d2m1eqxm1d2
  let cX: class X


  assert |- ( X e. CC -> ( ( ( X + 1 ) / 2 ) - 1 ) = ( ( X - 1 ) / 2 ) )

  proof
    cX
    cc
    wcel
    #
    cX
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cX
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    c2
    @0
    @2
    cc
    wcel
    @3
    cc
    wcel
    @0
    @1
    cX
    peano2cn
    #
    halfcld
    #
    @2
    peano2cnm
    syl
    @0
    @4
    cX
    peano2cnm
    #
    halfcld
    @0
    2cnd
    #
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    @0
    @3
    c2
    cmul
    co
    @2
    c2
    cmul
    co
    #
    c1
    c2
    cmul
    co
    #
    cmin
    co
    @1
    c2
    cmin
    co
    #
    @5
    c2
    cmul
    co
    #
    @0
    @2
    c1
    c2
    @7
    @0
    1cnd
    #
    @9
    subdird
    @0
    @11
    @1
    @12
    c2
    cmin
    @0
    @1
    c2
    @6
    @9
    @10
    divcan1d
    @0
    c2
    @9
    mulid2d
    oveq12d
    @0
    @14
    @4
    cX
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @13
    @0
    @4
    c2
    @8
    @9
    @10
    divcan1d
    @0
    @16
    c1
    cX
    cmin
    @16
    c1
    wceq
    @0
    2m1e1
    a1i
    oveq2d
    @0
    cX
    c2
    c1
    @0
    id
    @9
    @15
    subsub3d
    3eqtr2rd
    3eqtrd
    mulcan2ad
end
