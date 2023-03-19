include "cc.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wcel.mm"
include "wss.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "a1i.mm"
include "id.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "syl.mm"
include "addcncf.mm"
include "syl5eqel.mm"

theorem add1cncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume add1cncf.a: |- ( ph -> A e. CC )
  assume add1cncf.f: |- F = ( x e. CC |-> ( x + A ) )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F e. ( CC -cn-> CC ) )

  proof
    wph
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
    add1cncf.f
    wph
    vx
    @0
    cA
    cc
    vx
    cc
    @0
    cmpt
    @1
    wcel
    #
    wph
    cc
    cc
    wss
    #
    @3
    @2
    cc
    ssid
    #
    @4
    vx
    cc
    cc
    cncfmptid
    mp2an
    a1i
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
    add1cncf.a
    @5
    @5
    @3
    @3
    @6
    @5
    id
    @3
    @5
    @4
    a1i
    #
    @7
    vx
    cA
    cc
    cc
    cncfmptc
    syl3anc
    syl
    addcncf
    syl5eqel
end
