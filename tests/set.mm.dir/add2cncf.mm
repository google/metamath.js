include "cc.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wcel.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cncfmptc.mm"
include "mpd3an23.mm"
include "syl.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "addcncf.mm"
include "syl5eqel.mm"

theorem add2cncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume add2cncf.a: |- ( ph -> A e. CC )
  assume add2cncf.f: |- F = ( x e. CC |-> ( A + x ) )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F e. ( CC -cn-> CC ) )

  proof
    wph
    cF
    vx
    cc
    cA
    vx
    cv
    #
    caddc
    co
    cmpt
    cc
    cc
    ccncf
    co
    #
    add2cncf.f
    wph
    vx
    cA
    @0
    cc
    wph
    cA
    cc
    wcel
    #
    vx
    cc
    cA
    cmpt
    @1
    wcel
    #
    add2cncf.a
    @2
    cc
    cc
    wss
    #
    @4
    @3
    @4
    @2
    cc
    ssid
    #
    a1i
    #
    @6
    vx
    cA
    cc
    cc
    cncfmptc
    mpd3an23
    syl
    vx
    cc
    @0
    cmpt
    @1
    wcel
    #
    wph
    @4
    @4
    @7
    @5
    @5
    vx
    cc
    cc
    cncfmptid
    mp2an
    a1i
    addcncf
    syl5eqel
end
