include "cneg.mm"
include "cmpt.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "df-neg.mm"
include "a1i.mm"
include "mpteq2dva.mm"
include "eqid.mm"
include "0cn.mm"
include "wss.mm"
include "ssid.mm"
include "id.mm"
include "constcncfg.mm"
include "mp1i.mm"
include "cncfrss.mm"
include "syl.mm"
include "cncfmptssg.mm"
include "subcncf.mm"
include "eqeltrd.mm"

theorem negcncfg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume negcncfg.1: |- ( ph -> ( x e. A |-> B ) e. ( A -cn-> CC ) )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> -u B ) e. ( A -cn-> CC ) )

  proof
    wph
    vx
    cA
    cB
    cneg
    #
    cmpt
    vx
    cA
    cc0
    cB
    cmin
    co
    #
    cmpt
    cA
    cc
    ccncf
    co
    #
    wph
    vx
    cA
    @0
    @1
    @0
    @1
    wceq
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    df-neg
    a1i
    mpteq2dva
    wph
    vx
    cc0
    cB
    cA
    wph
    vx
    cc
    cc
    cA
    cc
    cc0
    vx
    cc
    cc0
    cmpt
    #
    @4
    eqid
    cc0
    cc
    wcel
    #
    @4
    cc
    cc
    ccncf
    co
    wcel
    wph
    0cn
    @5
    vx
    cc
    cc0
    cc
    cc
    cc
    wss
    #
    @5
    cc
    ssid
    #
    a1i
    #
    @5
    id
    @8
    constcncfg
    mp1i
    wph
    vx
    cA
    cB
    cmpt
    #
    @2
    wcel
    cA
    cc
    wss
    negcncfg.1
    cA
    cc
    @9
    cncfrss
    syl
    @6
    wph
    @7
    a1i
    @5
    @3
    0cn
    a1i
    cncfmptssg
    negcncfg.1
    subcncf
    eqeltrd
end
