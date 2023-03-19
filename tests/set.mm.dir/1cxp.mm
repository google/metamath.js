include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "cxpef.mm"
include "mp3an12.mm"
include "log1.mm"
include "oveq2i.mm"
include "mul01.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "ef0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem 1cxp
  let cA: class A


  assert |- ( A e. CC -> ( 1 ^c A ) = 1 )

  proof
    cA
    cc
    wcel
    #
    c1
    cA
    ccxp
    co
    #
    cA
    c1
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    c1
    cc
    wcel
    c1
    cc0
    wne
    @0
    @1
    @4
    wceq
    ax-1cn
    ax-1ne0
    c1
    cA
    cxpef
    mp3an12
    @0
    @4
    cc0
    ce
    cfv
    c1
    @0
    @3
    cc0
    ce
    @0
    @3
    cA
    cc0
    cmul
    co
    cc0
    @2
    cc0
    cA
    cmul
    log1
    oveq2i
    cA
    mul01
    syl5eq
    fveq2d
    ef0
    syl6eq
    eqtrd
end
