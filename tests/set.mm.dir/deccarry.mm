include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cdc.mm"
include "c9.mm"
include "cmul.mm"
include "df-dec.mm"
include "9nn.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "a1i.mm"
include "nnmulcld.mm"
include "nncnd.mm"
include "addid1d.mm"
include "cc.mm"
include "nncni.mm"
include "nncn.mm"
include "1cnd.mm"
include "adddid.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "oveq1i.mm"
include "id.mm"
include "addassd.mm"
include "syl5req.mm"
include "eqtrd.mm"

theorem deccarry
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. NN -> ( ; A 9 + 1 ) = ; ( A + 1 ) 0 )

  proof
    cA
    cn
    wcel
    #
    cA
    c1
    caddc
    co
    #
    cc0
    cdc
    c9
    c1
    caddc
    co
    #
    @1
    cmul
    co
    #
    cc0
    caddc
    co
    #
    cA
    c9
    cdc
    #
    c1
    caddc
    co
    #
    @1
    cc0
    df-dec
    @0
    @4
    @3
    @6
    @0
    @3
    @0
    @3
    @0
    @2
    @1
    @2
    cn
    wcel
    #
    @0
    c9
    cn
    wcel
    @7
    9nn
    c9
    peano2nn
    ax-mp
    #
    a1i
    #
    cA
    peano2nn
    nnmulcld
    nncnd
    addid1d
    @0
    @3
    @2
    cA
    cmul
    co
    #
    @2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @6
    @0
    @2
    cA
    c1
    @2
    cc
    wcel
    @0
    @2
    @8
    nncni
    a1i
    #
    cA
    nncn
    @0
    1cnd
    #
    adddid
    @0
    @12
    @10
    @2
    caddc
    co
    #
    @6
    @0
    @11
    @2
    @10
    caddc
    @0
    @2
    @13
    mulid1d
    oveq2d
    @0
    @6
    @10
    c9
    caddc
    co
    #
    c1
    caddc
    co
    @15
    @5
    @16
    c1
    caddc
    cA
    c9
    df-dec
    oveq1i
    @0
    @10
    c9
    c1
    @0
    @10
    @0
    @2
    cA
    @9
    @0
    id
    nnmulcld
    nncnd
    c9
    cc
    wcel
    @0
    c9
    9nn
    nncni
    a1i
    @14
    addassd
    syl5req
    eqtrd
    eqtrd
    eqtrd
    syl5req
end
