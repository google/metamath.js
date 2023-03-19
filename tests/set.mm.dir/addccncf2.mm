include "cc.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "simpl.mm"
include "simpr.mm"
include "ssid.mm"
include "a1i.mm"
include "constcncfg.mm"
include "cncfmptid.mm"
include "mpan2.mm"
include "adantr.mm"
include "addcncf.mm"
include "syl5eqel.mm"

theorem addccncf2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  assume addccncf2.1: |- F = ( x e. A |-> ( B + x ) )

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ( A C_ CC /\ B e. CC ) -> F e. ( A -cn-> CC ) )

  proof
    cA
    cc
    wss
    #
    cB
    cc
    wcel
    #
    wa
    #
    cF
    vx
    cA
    cB
    vx
    cv
    #
    caddc
    co
    cmpt
    cA
    cc
    ccncf
    co
    #
    addccncf2.1
    @2
    vx
    cB
    @3
    cA
    @2
    vx
    cA
    cB
    cc
    @0
    @1
    simpl
    @0
    @1
    simpr
    cc
    cc
    wss
    #
    @2
    cc
    ssid
    #
    a1i
    constcncfg
    @0
    vx
    cA
    @3
    cmpt
    @4
    wcel
    #
    @1
    @0
    @5
    @7
    @6
    vx
    cA
    cc
    cncfmptid
    mpan2
    adantr
    addcncf
    syl5eqel
end
