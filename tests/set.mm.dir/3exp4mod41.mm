include "c3.mm"
include "c4.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdc.mm"
include "cmo.mm"
include "c8.mm"
include "c2.mm"
include "cmul.mm"
include "cneg.mm"
include "caddc.mm"
include "2p2e4.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "3cn.mm"
include "2nn0.mm"
include "expadd.mm"
include "mp3an.mm"
include "c9.mm"
include "sq3.mm"
include "oveq12i.mm"
include "9t9e81.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "cc0.mm"
include "dfdec10.mm"
include "4cn.mm"
include "2cn.mm"
include "4t2e8.mm"
include "mulcomli.mm"
include "cmin.mm"
include "ax-1cn.mm"
include "negsubi.mm"
include "2m1e1.mm"
include "10nn.mm"
include "nncni.mm"
include "mulcli.mm"
include "neg1cn.mm"
include "addassi.mm"
include "adddii.mm"
include "mul12i.mm"
include "2t1e2.mm"
include "3eqtr3ri.mm"
include "3eqtr2i.mm"
include "4nn0.mm"
include "1nn.mm"
include "decnncl.mm"
include "addcomi.mm"
include "cr.mm"
include "crp.mm"
include "cz.mm"
include "neg1rr.mm"
include "cn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "2z.mm"
include "modcyc.mm"

theorem 3exp4mod41
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 3 ^ 4 ) mod ; 4 1 ) = ( -u 1 mod ; 4 1 )

  proof
    c3
    c4
    cexp
    co
    #
    c4
    c1
    cdc
    #
    cmo
    co
    c8
    c1
    cdc
    #
    @1
    cmo
    co
    c2
    @1
    cmul
    co
    #
    c1
    cneg
    #
    caddc
    co
    #
    @1
    cmo
    co
    #
    @4
    @1
    cmo
    co
    #
    @0
    @2
    @1
    cmo
    @0
    c3
    c2
    c2
    caddc
    co
    #
    cexp
    co
    #
    c3
    c2
    cexp
    co
    #
    @10
    cmul
    co
    #
    @2
    c4
    @8
    c3
    cexp
    @8
    c4
    2p2e4
    eqcomi
    oveq2i
    c3
    cc
    wcel
    c2
    cn0
    wcel
    #
    @12
    @9
    @11
    wceq
    3cn
    2nn0
    2nn0
    c3
    c2
    c2
    expadd
    mp3an
    @11
    c9
    c9
    cmul
    co
    @2
    @10
    c9
    @10
    c9
    cmul
    sq3
    sq3
    oveq12i
    9t9e81
    eqtri
    3eqtri
    oveq1i
    @2
    @5
    @1
    cmo
    @2
    c1
    cc0
    cdc
    #
    c8
    cmul
    co
    #
    c1
    caddc
    co
    #
    @5
    c8
    c1
    dfdec10
    @15
    @13
    c2
    c4
    cmul
    co
    #
    cmul
    co
    #
    c2
    @4
    caddc
    co
    #
    caddc
    co
    @17
    c2
    caddc
    co
    #
    @4
    caddc
    co
    @5
    @14
    @17
    c1
    @18
    caddc
    c8
    @16
    @13
    cmul
    @16
    c8
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    eqcomi
    oveq2i
    @18
    c1
    @18
    c2
    c1
    cmin
    co
    c1
    c2
    c1
    2cn
    ax-1cn
    negsubi
    2m1e1
    eqtri
    eqcomi
    oveq12i
    @17
    c2
    @4
    @13
    @16
    @13
    10nn
    nncni
    #
    c2
    c4
    2cn
    4cn
    mulcli
    mulcli
    2cn
    neg1cn
    addassi
    @19
    @3
    @4
    caddc
    c2
    @13
    c4
    cmul
    co
    #
    c1
    caddc
    co
    #
    cmul
    co
    c2
    @21
    cmul
    co
    #
    c2
    c1
    cmul
    co
    #
    caddc
    co
    @3
    @19
    c2
    @21
    c1
    2cn
    @13
    c4
    @20
    4cn
    mulcli
    ax-1cn
    adddii
    @22
    @1
    c2
    cmul
    @1
    @22
    c4
    c1
    dfdec10
    eqcomi
    oveq2i
    @23
    @17
    @24
    c2
    caddc
    c2
    @13
    c4
    2cn
    @20
    4cn
    mul12i
    2t1e2
    oveq12i
    3eqtr3ri
    oveq1i
    3eqtr2i
    eqtri
    oveq1i
    @6
    @4
    @3
    caddc
    co
    #
    @1
    cmo
    co
    #
    @7
    @5
    @25
    @1
    cmo
    @3
    @4
    c2
    @1
    2cn
    @1
    c4
    c1
    4nn0
    1nn
    decnncl
    #
    nncni
    mulcli
    neg1cn
    addcomi
    oveq1i
    @4
    cr
    wcel
    @1
    crp
    wcel
    #
    c2
    cz
    wcel
    @26
    @7
    wceq
    neg1rr
    @1
    cn
    wcel
    @28
    @27
    @1
    nnrp
    ax-mp
    2z
    @4
    @1
    c2
    modcyc
    mp3an
    eqtri
    3eqtri
end
