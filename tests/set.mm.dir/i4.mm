include "ci.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "c4.mm"
include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "ax-icn.mm"
include "2nn0.mm"
include "expadd.mm"
include "mp3an.mm"
include "2p2e4.mm"
include "oveq2i.mm"
include "cneg.mm"
include "i2.mm"
include "oveq12i.mm"
include "ax-1cn.mm"
include "mul2negi.mm"
include "1t1e1.mm"
include "3eqtri.mm"
include "3eqtr3i.mm"

theorem i4



  assert |- ( _i ^ 4 ) = 1

  proof
    ci
    c2
    c2
    caddc
    co
    #
    cexp
    co
    #
    ci
    c2
    cexp
    co
    #
    @2
    cmul
    co
    #
    ci
    c4
    cexp
    co
    c1
    ci
    cc
    wcel
    c2
    cn0
    wcel
    #
    @4
    @1
    @3
    wceq
    ax-icn
    2nn0
    2nn0
    ci
    c2
    c2
    expadd
    mp3an
    @0
    c4
    ci
    cexp
    2p2e4
    oveq2i
    @3
    c1
    cneg
    #
    @5
    cmul
    co
    c1
    c1
    cmul
    co
    c1
    @2
    @5
    @2
    @5
    cmul
    i2
    i2
    oveq12i
    c1
    c1
    ax-1cn
    ax-1cn
    mul2negi
    1t1e1
    3eqtri
    3eqtr3i
end
