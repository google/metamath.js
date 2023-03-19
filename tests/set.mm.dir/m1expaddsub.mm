include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cc.mm"
include "m1expcl.mm"
include "zcnd.mm"
include "adantr.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "expne0i.mm"
include "mp3an12.mm"
include "divrecd.mm"
include "wceq.mm"
include "cpr.mm"
include "wo.mm"
include "m1expcl2.mm"
include "elpri.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "divneg2.mm"
include "mp3an.mm"
include "1div1e1.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "oveq2.mm"
include "id.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "3syl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "expsub.mm"
include "mpanl12.mm"
include "expaddz.mm"
include "3eqtr4d.mm"

theorem m1expaddsub
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. ZZ /\ Y e. ZZ ) -> ( -u 1 ^ ( X - Y ) ) = ( -u 1 ^ ( X + Y ) ) )

  proof
    cX
    cz
    wcel
    #
    cY
    cz
    wcel
    #
    wa
    #
    c1
    cneg
    #
    cX
    cexp
    co
    #
    @3
    cY
    cexp
    co
    #
    cdiv
    co
    #
    @4
    @5
    cmul
    co
    #
    @3
    cX
    cY
    cmin
    co
    cexp
    co
    #
    @3
    cX
    cY
    caddc
    co
    cexp
    co
    #
    @2
    @6
    @4
    c1
    @5
    cdiv
    co
    #
    cmul
    co
    @7
    @2
    @4
    @5
    @0
    @4
    cc
    wcel
    @1
    @0
    @4
    cX
    m1expcl
    zcnd
    adantr
    @1
    @5
    cc
    wcel
    @0
    @1
    @5
    cY
    m1expcl
    zcnd
    adantl
    @1
    @5
    cc0
    wne
    #
    @0
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    @1
    @11
    neg1cn
    neg1ne0
    @3
    cY
    expne0i
    mp3an12
    adantl
    divrecd
    @2
    @10
    @5
    @4
    cmul
    @1
    @10
    @5
    wceq
    #
    @0
    @1
    @5
    @3
    c1
    cpr
    wcel
    @5
    @3
    wceq
    #
    @5
    c1
    wceq
    #
    wo
    @14
    cY
    m1expcl2
    @5
    @3
    c1
    elpri
    @15
    @14
    @16
    @15
    c1
    @3
    cdiv
    co
    #
    @3
    @10
    @5
    c1
    c1
    cdiv
    co
    #
    cneg
    #
    @17
    @3
    c1
    cc
    wcel
    #
    @20
    c1
    cc0
    wne
    @19
    @17
    wceq
    ax-1cn
    ax-1cn
    ax-1ne0
    c1
    c1
    divneg2
    mp3an
    @18
    c1
    1div1e1
    negeqi
    eqtr3i
    @5
    @3
    c1
    cdiv
    oveq2
    @15
    id
    3eqtr4a
    @16
    @18
    c1
    @10
    @5
    1div1e1
    @5
    c1
    c1
    cdiv
    oveq2
    @16
    id
    3eqtr4a
    jaoi
    3syl
    adantl
    oveq2d
    eqtrd
    @12
    @13
    @2
    @8
    @6
    wceq
    neg1cn
    neg1ne0
    @3
    cX
    cY
    expsub
    mpanl12
    @12
    @13
    @2
    @9
    @7
    wceq
    neg1cn
    neg1ne0
    @3
    cX
    cY
    expaddz
    mpanl12
    3eqtr4d
end
