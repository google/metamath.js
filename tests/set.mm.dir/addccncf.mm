include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "addcn.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "cncfmptc.mm"
include "mp3an23.mm"
include "cncfmpt2f.mm"
include "syl5eqel.mm"

theorem addccncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume addccncf.1: |- F = ( x e. CC |-> ( x + A ) )

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
    caddc
    co
    cmpt
    cc
    cc
    ccncf
    co
    #
    addccncf.1
    @0
    vx
    @1
    cA
    caddc
    ccnfld
    ctopn
    cfv
    #
    cc
    @3
    eqid
    #
    caddc
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
    addcn
    a1i
    vx
    cc
    @1
    cmpt
    @2
    wcel
    #
    @0
    cc
    cc
    wss
    #
    @6
    @5
    cc
    ssid
    #
    @7
    vx
    cc
    cc
    cncfmptid
    mp2an
    a1i
    @0
    @6
    @6
    vx
    cc
    cA
    cmpt
    @2
    wcel
    @7
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
