include "c3.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmo.mm"
include "cc0.mm"
include "cdc.mm"
include "cneg.mm"
include "41prothprmlem1.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "c4.mm"
include "c5.mm"
include "cmul.mm"
include "5cn.mm"
include "4cn.mm"
include "5t4e20.mm"
include "mulcomli.mm"
include "eqcomi.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "3cn.mm"
include "4nn0.mm"
include "5nn0.mm"
include "expmul.mm"
include "mp3an.mm"
include "eqtri.mm"
include "cz.mm"
include "wa.mm"
include "crp.mm"
include "3z.mm"
include "zexpcl.mm"
include "mp2an.mm"
include "neg1z.mm"
include "pm3.2i.mm"
include "cn.mm"
include "1nn.mm"
include "decnncl.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "3exp4mod41.mm"
include "modexp.mm"
include "caddc.mm"
include "3p2e5.mm"
include "2z.mm"
include "m1expaddsub.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "2p1e3.mm"
include "subaddrii.mm"
include "neg1cn.mm"
include "exp1.mm"
include "3eqtri.mm"
include "3eqtr4i.mm"

theorem 41prothprmlem2
  let cP: class P
  let vk: setvar k
  let vx: setvar x
  assume 41prothprm.p: |- P = ; 4 1


  assert |- ( ( 3 ^ ( ( P - 1 ) / 2 ) ) mod P ) = ( -u 1 mod P )

  proof
    c3
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    c3
    c2
    cc0
    cdc
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    cneg
    #
    cP
    cmo
    co
    #
    @1
    @3
    cP
    cmo
    @0
    @2
    c3
    cexp
    cP
    41prothprm.p
    41prothprmlem1
    oveq2i
    oveq1i
    @3
    c4
    c1
    cdc
    #
    cmo
    co
    #
    @5
    @7
    cmo
    co
    #
    @4
    @6
    @8
    c3
    c4
    cexp
    co
    #
    c5
    cexp
    co
    #
    @7
    cmo
    co
    #
    @5
    c5
    cexp
    co
    #
    @7
    cmo
    co
    #
    @9
    @3
    @11
    @7
    cmo
    @3
    c3
    c4
    c5
    cmul
    co
    #
    cexp
    co
    #
    @11
    @2
    @15
    c3
    cexp
    @15
    @2
    c5
    c4
    @2
    5cn
    4cn
    5t4e20
    mulcomli
    eqcomi
    oveq2i
    c3
    cc
    wcel
    c4
    cn0
    wcel
    #
    c5
    cn0
    wcel
    #
    @16
    @11
    wceq
    3cn
    4nn0
    5nn0
    c3
    c4
    c5
    expmul
    mp3an
    eqtri
    oveq1i
    @10
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    wa
    @18
    @7
    crp
    wcel
    #
    wa
    @10
    @7
    cmo
    co
    @9
    wceq
    @12
    @14
    wceq
    @19
    @20
    c3
    cz
    wcel
    #
    @17
    @19
    3z
    4nn0
    c3
    c4
    zexpcl
    mp2an
    neg1z
    pm3.2i
    @18
    @21
    5nn0
    @7
    cn
    wcel
    @21
    c4
    c1
    4nn0
    1nn
    decnncl
    @7
    nnrp
    ax-mp
    pm3.2i
    3exp4mod41
    @10
    @5
    c5
    @7
    modexp
    mp3an
    @13
    @5
    @7
    cmo
    @13
    @5
    c3
    c2
    caddc
    co
    #
    cexp
    co
    #
    @5
    c3
    c2
    cmin
    co
    #
    cexp
    co
    #
    @5
    c5
    @23
    @5
    cexp
    @23
    c5
    3p2e5
    eqcomi
    oveq2i
    @26
    @24
    @22
    c2
    cz
    wcel
    @26
    @24
    wceq
    3z
    2z
    c3
    c2
    m1expaddsub
    mp2an
    eqcomi
    @26
    @5
    c1
    cexp
    co
    #
    @5
    @25
    c1
    @5
    cexp
    c3
    c2
    c1
    3cn
    2cn
    ax-1cn
    2p1e3
    subaddrii
    oveq2i
    @5
    cc
    wcel
    @27
    @5
    wceq
    neg1cn
    @5
    exp1
    ax-mp
    eqtri
    3eqtri
    oveq1i
    3eqtri
    cP
    @7
    @3
    cmo
    41prothprm.p
    oveq2i
    cP
    @7
    @5
    cmo
    41prothprm.p
    oveq2i
    3eqtr4i
    eqtri
end
