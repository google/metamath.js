include "c6.mm"
include "c4.mm"
include "clcm.mm"
include "co.mm"
include "cmul.mm"
include "cgcd.mm"
include "cdiv.mm"
include "c2.mm"
include "c1.mm"
include "cdc.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "6cn.mm"
include "4cn.mm"
include "mulcli.mm"
include "cz.mm"
include "6nn0.mm"
include "nn0zi.mm"
include "4z.mm"
include "pm3.2i.mm"
include "lcmcl.mm"
include "nn0cnd.mm"
include "ax-mp.mm"
include "gcdcl.mm"
include "wn.mm"
include "cn.mm"
include "4ne0.mm"
include "neii.mm"
include "intnan.mm"
include "gcdn0cl.mm"
include "nnne0i.mm"
include "w3a.mm"
include "6nn.mm"
include "4nn.mm"
include "lcmgcdnn.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "divmul3.mm"
include "mpbird.mm"
include "mp3an.mm"
include "6gcd4e2.mm"
include "oveq2i.mm"
include "2cn.mm"
include "2ne0.mm"
include "divassi.mm"
include "4d2e2.mm"
include "6t2e12.mm"
include "3eqtri.mm"

theorem 6lcm4e12



  assert |- ( 6 lcm 4 ) = ; 1 2

  proof
    c6
    c4
    clcm
    co
    #
    c6
    c4
    cmul
    co
    #
    c6
    c4
    cgcd
    co
    #
    cdiv
    co
    #
    @1
    c2
    cdiv
    co
    #
    c1
    c2
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
    c6
    c4
    6cn
    4cn
    mulcli
    c6
    cz
    wcel
    #
    c4
    cz
    wcel
    #
    wa
    #
    @7
    @11
    @12
    c6
    6nn0
    nn0zi
    4z
    pm3.2i
    #
    @13
    @0
    c6
    c4
    lcmcl
    nn0cnd
    ax-mp
    @8
    @9
    @13
    @8
    @14
    @13
    @2
    c6
    c4
    gcdcl
    nn0cnd
    ax-mp
    @2
    @13
    c6
    cc0
    wceq
    #
    c4
    cc0
    wceq
    #
    wa
    wn
    #
    wa
    @2
    cn
    wcel
    @13
    @17
    @14
    @16
    @15
    c4
    cc0
    4ne0
    neii
    intnan
    pm3.2i
    c6
    c4
    gcdn0cl
    ax-mp
    nnne0i
    pm3.2i
    @6
    @7
    @10
    w3a
    #
    @3
    @0
    @18
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
    @18
    @19
    @1
    c6
    cn
    wcel
    #
    c4
    cn
    wcel
    #
    wa
    @19
    @1
    wceq
    @18
    @20
    @21
    6nn
    4nn
    pm3.2i
    c6
    c4
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
    c2
    @1
    cdiv
    6gcd4e2
    oveq2i
    @4
    c6
    c4
    c2
    cdiv
    co
    #
    cmul
    co
    c6
    c2
    cmul
    co
    @5
    c6
    c4
    c2
    6cn
    4cn
    2cn
    2ne0
    divassi
    @22
    c2
    c6
    cmul
    4d2e2
    oveq2i
    6t2e12
    3eqtri
    3eqtri
end
