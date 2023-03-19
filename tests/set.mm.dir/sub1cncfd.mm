include "cc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wcel.mm"
include "wss.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "a1i.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "subcncf.mm"
include "syl5eqel.mm"

theorem sub1cncfd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume sub1cncfd.1: |- ( ph -> A e. CC )
  assume sub1cncfd.2: |- F = ( x e. CC |-> ( x - A ) )

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
    cmin
    co
    cmpt
    cc
    cc
    ccncf
    co
    #
    sub1cncfd.2
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
    @3
    @3
    vx
    cc
    cA
    cmpt
    @1
    wcel
    sub1cncfd.1
    @3
    wph
    @4
    a1i
    #
    @5
    vx
    cA
    cc
    cc
    cncfmptc
    syl3anc
    subcncf
    syl5eqel
end
