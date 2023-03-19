include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "cmul.mm"
include "csm.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "ax-hvmul0.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "cc.mm"
include "0cn.mm"
include "ax-his3.mm"
include "mp3an12.mm"
include "syl5eqr.mm"
include "hicl.mm"
include "mpan.mm"
include "mul02d.mm"
include "eqtrd.mm"

theorem hi01
  let cA: class A


  assert |- ( A e. ~H -> ( 0h .ih A ) = 0 )

  proof
    cA
    chil
    wcel
    #
    c0v
    cA
    csp
    co
    #
    cc0
    @1
    cmul
    co
    #
    cc0
    @0
    @1
    cc0
    c0v
    csm
    co
    #
    cA
    csp
    co
    #
    @2
    @3
    c0v
    cA
    csp
    c0v
    chil
    wcel
    #
    @3
    c0v
    wceq
    ax-hv0cl
    c0v
    ax-hvmul0
    ax-mp
    oveq1i
    cc0
    cc
    wcel
    @5
    @0
    @4
    @2
    wceq
    0cn
    ax-hv0cl
    cc0
    c0v
    cA
    ax-his3
    mp3an12
    syl5eqr
    @0
    @1
    @5
    @0
    @1
    cc
    wcel
    ax-hv0cl
    c0v
    cA
    hicl
    mpan
    mul02d
    eqtrd
end
