include "c2.mm"
include "c5.mm"
include "cexp.mm"
include "co.mm"
include "c8.mm"
include "c4.mm"
include "cmul.mm"
include "c3.mm"
include "cdc.mm"
include "caddc.mm"
include "3p2e5.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "2cn.mm"
include "3nn0.mm"
include "2nn0.mm"
include "expadd.mm"
include "mp3an.mm"
include "cu2.mm"
include "sq2.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "8t4e32.mm"

theorem 2exp5
  let vk: setvar k
  let vx: setvar x


  assert |- ( 2 ^ 5 ) = ; 3 2

  proof
    c2
    c5
    cexp
    co
    #
    c8
    c4
    cmul
    co
    #
    c3
    c2
    cdc
    @0
    c2
    c3
    c2
    caddc
    co
    #
    cexp
    co
    #
    @1
    c5
    @2
    c2
    cexp
    @2
    c5
    3p2e5
    eqcomi
    oveq2i
    @3
    c2
    c3
    cexp
    co
    #
    c2
    c2
    cexp
    co
    #
    cmul
    co
    #
    @1
    c2
    cc
    wcel
    c3
    cn0
    wcel
    c2
    cn0
    wcel
    @3
    @6
    wceq
    2cn
    3nn0
    2nn0
    c2
    c3
    c2
    expadd
    mp3an
    @4
    c8
    @5
    c4
    cmul
    cu2
    sq2
    oveq12i
    eqtri
    eqtri
    8t4e32
    eqtri
end
