include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "subcn.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "mp3an23.mm"
include "idcncf.mm"
include "cncfmpt2f.mm"
include "syl5eqel.mm"

theorem sub2cncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume sub2cncf.1: |- F = ( x e. CC |-> ( A - x ) )

  disjoint A x
  assert |- ( A e. CC -> F e. ( CC -cn-> CC ) )

  proof
    cA
    cc
    wcel
    #
    cF
    vx
    cc
    cA
    vx
    cv
    #
    cmin
    co
    cmpt
    cc
    cc
    ccncf
    co
    #
    sub2cncf.1
    @0
    vx
    cA
    @1
    cmin
    ccnfld
    ctopn
    cfv
    #
    cc
    @3
    eqid
    #
    cmin
    @3
    @3
    ctx
    co
    @3
    ccn
    co
    wcel
    @0
    @3
    @4
    subcn
    a1i
    @0
    cc
    cc
    wss
    #
    @5
    vx
    cc
    cA
    cmpt
    @2
    wcel
    cc
    ssid
    #
    @6
    vx
    cA
    cc
    cc
    cncfmptc
    mp3an23
    vx
    cc
    @1
    cmpt
    #
    @2
    wcel
    @0
    vx
    @7
    @7
    eqid
    idcncf
    a1i
    cncfmpt2f
    syl5eqel
end
