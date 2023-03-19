include "c3.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmo.mm"
include "cneg.mm"
include "wceq.mm"
include "c5.mm"
include "cmul.mm"
include "caddc.mm"
include "cprime.mm"
include "wcel.mm"
include "wa.mm"
include "41prothprmlem2.mm"
include "c4.mm"
include "cdc.mm"
include "cc0.mm"
include "dfdec10.mm"
include "c8.mm"
include "4t2e8.mm"
include "4cn.mm"
include "2cn.mm"
include "mulcomi.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "5cn.mm"
include "mulassi.mm"
include "5t2e10.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"
include "cu2.mm"
include "eqcomi.mm"
include "3eqtri.mm"
include "simpr.mm"
include "cn.mm"
include "3nn.mm"
include "a1i.mm"
include "5nn.mm"
include "clt.mm"
include "wbr.mm"
include "5lt8.mm"
include "breqtrri.mm"
include "cv.mm"
include "cz.mm"
include "wrex.mm"
include "3z.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "id.mm"
include "rspcedvd.mm"
include "adantr.mm"
include "proththd.mm"
include "jca.mm"
include "mp2an.mm"

theorem 41prothprm
  let cP: class P
  let vx: setvar x
  let vk: setvar k
  assume 41prothprm.p: |- P = ; 4 1


  assert |- ( P = ( ( 5 x. ( 2 ^ 3 ) ) + 1 ) /\ P e. Prime )

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
    #
    c1
    cneg
    cP
    cmo
    co
    #
    wceq
    #
    cP
    c5
    c2
    c3
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    @8
    cP
    cprime
    wcel
    #
    wa
    cP
    41prothprm.p
    41prothprmlem2
    cP
    c4
    c1
    cdc
    c1
    cc0
    cdc
    #
    c4
    cmul
    co
    #
    c1
    caddc
    co
    @7
    41prothprm.p
    c4
    c1
    dfdec10
    @11
    @6
    c1
    caddc
    c5
    c8
    cmul
    co
    #
    @11
    @6
    @12
    c5
    c2
    c4
    cmul
    co
    #
    cmul
    co
    c5
    c2
    cmul
    co
    #
    c4
    cmul
    co
    @11
    c8
    @13
    c5
    cmul
    c4
    c2
    cmul
    co
    c8
    @13
    4t2e8
    c4
    c2
    4cn
    2cn
    mulcomi
    eqtr3i
    oveq2i
    c5
    c2
    c4
    5cn
    2cn
    4cn
    mulassi
    @14
    @10
    c4
    cmul
    5t2e10
    oveq1i
    3eqtr2i
    c8
    @5
    c5
    cmul
    @5
    c8
    cu2
    eqcomi
    oveq2i
    eqtr3i
    oveq1i
    3eqtri
    @4
    @8
    wa
    #
    @8
    @9
    @4
    @8
    simpr
    #
    @15
    vx
    cP
    c5
    c3
    c3
    cn
    wcel
    @15
    3nn
    a1i
    c5
    cn
    wcel
    @15
    5nn
    a1i
    @16
    c5
    @5
    clt
    wbr
    @15
    c5
    c8
    @5
    clt
    5lt8
    cu2
    breqtrri
    a1i
    @4
    vx
    cv
    #
    @0
    cexp
    co
    #
    cP
    cmo
    co
    #
    @3
    wceq
    #
    vx
    cz
    wrex
    @8
    @4
    @20
    @4
    vx
    c3
    cz
    c3
    cz
    wcel
    @4
    3z
    a1i
    @17
    c3
    wceq
    #
    @20
    @4
    wb
    @4
    @21
    @19
    @2
    @3
    @21
    @18
    @1
    cP
    cmo
    @17
    c3
    @0
    cexp
    oveq1
    oveq1d
    eqeq1d
    adantl
    @4
    id
    rspcedvd
    adantr
    proththd
    jca
    mp2an
end
