include "cc.mm"
include "wcel.mm"
include "c0v.mm"
include "cc0.mm"
include "csm.mm"
include "co.mm"
include "cmul.mm"
include "mul01.mm"
include "oveq1d.mm"
include "chil.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "ax-hvmul0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "0cn.mm"
include "ax-hvmulass.mm"
include "mp3an23.mm"
include "eqtr3d.mm"
include "oveq2i.mm"
include "syl6req.mm"

theorem hvmul0
  let cA: class A


  assert |- ( A e. CC -> ( A .h 0h ) = 0h )

  proof
    cA
    cc
    wcel
    #
    c0v
    cA
    cc0
    c0v
    csm
    co
    #
    csm
    co
    #
    cA
    c0v
    csm
    co
    @0
    cA
    cc0
    cmul
    co
    #
    c0v
    csm
    co
    #
    c0v
    @2
    @0
    @4
    @1
    c0v
    @0
    @3
    cc0
    c0v
    csm
    cA
    mul01
    oveq1d
    c0v
    chil
    wcel
    #
    @1
    c0v
    wceq
    ax-hv0cl
    c0v
    ax-hvmul0
    ax-mp
    #
    syl6eq
    @0
    cc0
    cc
    wcel
    @5
    @4
    @2
    wceq
    0cn
    ax-hv0cl
    cA
    cc0
    c0v
    ax-hvmulass
    mp3an23
    eqtr3d
    @1
    c0v
    cA
    csm
    @6
    oveq2i
    syl6req
end
