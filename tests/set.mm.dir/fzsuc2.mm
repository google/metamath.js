include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wceq.mm"
include "caddc.mm"
include "wo.mm"
include "cfz.mm"
include "csn.mm"
include "cun.mm"
include "uzp1.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "c0.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "clt.mm"
include "wbr.mm"
include "zre.mm"
include "ltm1d.mm"
include "wb.mm"
include "peano2zm.mm"
include "fzn.mm"
include "mpdan.mm"
include "mpbid.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "fzsn.mm"
include "3eqtr4a.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wa.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "fzsuc.mm"
include "syl.mm"
include "jaodan.mm"
include "sylan2.mm"

theorem fzsuc2
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ( ZZ>= ` ( M - 1 ) ) ) -> ( M ... ( N + 1 ) ) = ( ( M ... N ) u. { ( N + 1 ) } ) )

  proof
    cN
    cM
    c1
    cmin
    co
    #
    cuz
    cfv
    wcel
    cM
    cz
    wcel
    #
    cN
    @0
    wceq
    #
    cN
    @0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wo
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cM
    cN
    cfz
    co
    #
    @6
    csn
    #
    cun
    #
    wceq
    #
    @0
    cN
    uzp1
    @1
    @2
    @11
    @5
    @1
    @2
    @11
    @1
    @11
    @2
    cM
    @3
    cfz
    co
    #
    cM
    @0
    cfz
    co
    #
    @3
    csn
    #
    cun
    #
    wceq
    @1
    @12
    cM
    cM
    cfz
    co
    #
    @15
    @1
    @3
    cM
    cM
    cfz
    @1
    cM
    cc
    wcel
    c1
    cc
    wcel
    @3
    cM
    wceq
    cM
    zcn
    ax-1cn
    cM
    c1
    npcan
    sylancl
    #
    oveq2d
    @1
    c0
    cM
    csn
    #
    cun
    #
    @18
    @15
    @16
    @19
    @18
    c0
    cun
    @18
    c0
    @18
    uncom
    @18
    un0
    eqtri
    @1
    @13
    c0
    @14
    @18
    @1
    @0
    cM
    clt
    wbr
    #
    @13
    c0
    wceq
    #
    @1
    cM
    cM
    zre
    ltm1d
    @1
    @0
    cz
    wcel
    @20
    @21
    wb
    cM
    peano2zm
    cM
    @0
    fzn
    mpdan
    mpbid
    @1
    @3
    cM
    @17
    sneqd
    uneq12d
    cM
    fzsn
    3eqtr4a
    eqtr4d
    @2
    @7
    @12
    @10
    @15
    @2
    @6
    @3
    cM
    cfz
    cN
    @0
    c1
    caddc
    oveq1
    #
    oveq2d
    @2
    @8
    @13
    @9
    @14
    cN
    @0
    cM
    cfz
    oveq2
    @2
    @6
    @3
    @22
    sneqd
    uneq12d
    eqeq12d
    syl5ibrcom
    imp
    @1
    @5
    wa
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @11
    @1
    @5
    @24
    @1
    @4
    @23
    cN
    @1
    @3
    cM
    cuz
    @17
    fveq2d
    eleq2d
    biimpa
    cM
    cN
    fzsuc
    syl
    jaodan
    sylan2
end
