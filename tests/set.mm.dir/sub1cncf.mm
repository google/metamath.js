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
include "idcncf.mm"
include "wss.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "mp3an23.mm"
include "cncfmpt2f.mm"
include "syl5eqel.mm"

theorem sub1cncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume sub1cncf.1: |- F = ( x e. CC |-> ( x - A ) )

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
    vx
    cv
    #
    cA
    cmin
    co
    cmpt
    cc
    cc
    ccncf
    co
    #
    sub1cncf.1
    @0
    vx
    @1
    cA
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
    vx
    cc
    @1
    cmpt
    #
    @2
    wcel
    @0
    vx
    @5
    @5
    eqid
    idcncf
    a1i
    @0
    cc
    cc
    wss
    #
    @6
    vx
    cc
    cA
    cmpt
    @2
    wcel
    cc
    ssid
    #
    @7
    vx
    cA
    cc
    cc
    cncfmptc
    mp3an23
    cncfmpt2f
    syl5eqel
end
