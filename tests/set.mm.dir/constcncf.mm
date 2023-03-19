include "cc.mm"
include "wcel.mm"
include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "wss.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "mp3an23.mm"
include "syl5eqel.mm"

theorem constcncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume constcncf.1: |- F = ( x e. CC |-> A )

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
    cmpt
    #
    cc
    cc
    ccncf
    co
    #
    constcncf.1
    @0
    cc
    cc
    wss
    #
    @3
    @1
    @2
    wcel
    cc
    ssid
    #
    @4
    vx
    cA
    cc
    cc
    cncfmptc
    mp3an23
    syl5eqel
end
