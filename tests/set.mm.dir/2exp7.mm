include "c2.mm"
include "c7.mm"
include "cexp.mm"
include "co.mm"
include "c6.mm"
include "c4.mm"
include "cdc.mm"
include "cmul.mm"
include "c1.mm"
include "c8.mm"
include "caddc.mm"
include "df-7.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "2cn.mm"
include "6nn0.mm"
include "expp1.mm"
include "mp2an.mm"
include "2exp6.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "2nn0.mm"
include "4nn0.mm"
include "eqid.mm"
include "8nn0.mm"
include "6t2e12.mm"
include "4t2e8.mm"
include "decmul1.mm"

theorem 2exp7
  let vk: setvar k
  let vx: setvar x


  assert |- ( 2 ^ 7 ) = ; ; 1 2 8

  proof
    c2
    c7
    cexp
    co
    #
    c6
    c4
    cdc
    #
    c2
    cmul
    co
    #
    c1
    c2
    cdc
    #
    c8
    cdc
    @0
    c2
    c6
    c1
    caddc
    co
    #
    cexp
    co
    #
    @2
    c7
    @4
    c2
    cexp
    df-7
    oveq2i
    @5
    c2
    c6
    cexp
    co
    #
    c2
    cmul
    co
    #
    @2
    c2
    cc
    wcel
    c6
    cn0
    wcel
    @5
    @7
    wceq
    2cn
    6nn0
    c2
    c6
    expp1
    mp2an
    @6
    @1
    c2
    cmul
    2exp6
    oveq1i
    eqtri
    eqtri
    c6
    c4
    @3
    c8
    c2
    @1
    2nn0
    6nn0
    4nn0
    @1
    eqid
    8nn0
    6t2e12
    4t2e8
    decmul1
    eqtri
end
