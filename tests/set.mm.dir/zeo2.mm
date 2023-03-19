include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wn.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "peano2cn.mm"
include "syl.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "zneo.mm"
include "expcom.mm"
include "necon2bd.mm"
include "syl5com.mm"
include "zeo.mm"
include "ord.mm"
include "con1d.mm"
include "impbid.mm"

theorem zeo2
  let cN: class N


  assert |- ( N e. ZZ -> ( ( N / 2 ) e. ZZ <-> -. ( ( N + 1 ) / 2 ) e. ZZ ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wn
    #
    @0
    c2
    @4
    cmul
    co
    #
    c2
    @1
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    @2
    @6
    @0
    @7
    @3
    @9
    @0
    @3
    c2
    @0
    cN
    cc
    wcel
    @3
    cc
    wcel
    cN
    zcn
    #
    cN
    peano2cn
    syl
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
    divcan2d
    @0
    @8
    cN
    c1
    caddc
    @0
    cN
    c2
    @10
    @11
    @12
    divcan2d
    oveq1d
    eqtr4d
    @2
    @5
    @7
    @9
    @5
    @2
    @7
    @9
    wne
    @4
    @1
    zneo
    expcom
    necon2bd
    syl5com
    @0
    @2
    @5
    @0
    @2
    @5
    cN
    zeo
    ord
    con1d
    impbid
end
