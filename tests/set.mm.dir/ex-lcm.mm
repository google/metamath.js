include "c6.mm"
include "c9.mm"
include "clcm.mm"
include "co.mm"
include "cmul.mm"
include "cgcd.mm"
include "cdiv.mm"
include "c3.mm"
include "c1.mm"
include "c8.mm"
include "cdc.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "6nn.mm"
include "9nn.mm"
include "nnmulcli.mm"
include "nncni.mm"
include "cz.mm"
include "nnzi.mm"
include "pm3.2i.mm"
include "lcmcl.mm"
include "nn0cnd.mm"
include "ax-mp.mm"
include "cneg.mm"
include "neggcd.mm"
include "eqcomi.mm"
include "ex-gcd.mm"
include "eqtri.mm"
include "3cn.mm"
include "eqeltri.mm"
include "3ne0.mm"
include "eqnetri.mm"
include "w3a.mm"
include "cn.mm"
include "lcmgcdnn.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "divmul3.mm"
include "mpbird.mm"
include "mp3an.mm"
include "oveq2i.mm"
include "6cn.mm"
include "9cn.mm"
include "divassi.mm"
include "3t3e9.mm"
include "oveq1i.mm"
include "divcan3i.mm"
include "6t3e18.mm"
include "3eqtri.mm"

theorem ex-lcm



  assert |- ( 6 lcm 9 ) = ; 1 8

  proof
    c6
    c9
    clcm
    co
    #
    c6
    c9
    cmul
    co
    #
    c6
    c9
    cgcd
    co
    #
    cdiv
    co
    #
    @1
    c3
    cdiv
    co
    #
    c1
    c8
    cdc
    #
    @1
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    #
    wa
    #
    @0
    @3
    wceq
    @1
    c6
    c9
    6nn
    9nn
    nnmulcli
    nncni
    c6
    cz
    wcel
    #
    c9
    cz
    wcel
    #
    wa
    #
    @7
    @11
    @12
    c6
    6nn
    nnzi
    c9
    9nn
    nnzi
    pm3.2i
    #
    @13
    @0
    c6
    c9
    lcmcl
    nn0cnd
    ax-mp
    @8
    @9
    @2
    c3
    cc
    @2
    c6
    cneg
    c9
    cgcd
    co
    #
    c3
    @15
    @2
    @13
    @15
    @2
    wceq
    @14
    c6
    c9
    neggcd
    ax-mp
    eqcomi
    ex-gcd
    eqtri
    #
    3cn
    eqeltri
    @2
    c3
    cc0
    @16
    3ne0
    eqnetri
    pm3.2i
    @6
    @7
    @10
    w3a
    #
    @3
    @0
    @17
    @3
    @0
    wceq
    @1
    @0
    @2
    cmul
    co
    #
    wceq
    @17
    @18
    @1
    c6
    cn
    wcel
    #
    c9
    cn
    wcel
    #
    wa
    @18
    @1
    wceq
    @17
    @19
    @20
    6nn
    9nn
    pm3.2i
    c6
    c9
    lcmgcdnn
    mp1i
    eqcomd
    @1
    @0
    @2
    divmul3
    mpbird
    eqcomd
    mp3an
    @2
    c3
    @1
    cdiv
    @16
    oveq2i
    @4
    c6
    c9
    c3
    cdiv
    co
    #
    cmul
    co
    c6
    c3
    cmul
    co
    @5
    c6
    c9
    c3
    6cn
    9cn
    3cn
    3ne0
    divassi
    @21
    c3
    c6
    cmul
    @21
    c3
    c3
    cmul
    co
    #
    c3
    cdiv
    co
    c3
    c9
    @22
    c3
    cdiv
    @22
    c9
    3t3e9
    eqcomi
    oveq1i
    c3
    c3
    3cn
    3cn
    3ne0
    divcan3i
    eqtri
    oveq2i
    6t3e18
    3eqtri
    3eqtri
end
