include "cc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wcel.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "subcncf.mm"
include "syl5eqel.mm"

theorem sub2cncfd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume sub2cncfd.1: |- ( ph -> A e. CC )
  assume sub2cncfd.2: |- F = ( x e. CC |-> ( A - x ) )

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
    cmin
    co
    cmpt
    cc
    cc
    ccncf
    co
    #
    sub2cncfd.2
    wph
    vx
    cA
    @0
    cc
    wph
    cA
    cc
    wcel
    cc
    cc
    wss
    #
    @2
    vx
    cc
    cA
    cmpt
    @1
    wcel
    sub2cncfd.1
    @2
    wph
    cc
    ssid
    #
    a1i
    #
    @4
    vx
    cA
    cc
    cc
    cncfmptc
    syl3anc
    vx
    cc
    @0
    cmpt
    @1
    wcel
    #
    wph
    @2
    @2
    @5
    @3
    @3
    vx
    cc
    cc
    cncfmptid
    mp2an
    a1i
    subcncf
    syl5eqel
end
