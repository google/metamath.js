include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "cncfmptc.mm"
include "syl3anc.mm"

theorem constcncfg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume constcncfg.a: |- ( ph -> A C_ CC )
  assume constcncfg.b: |- ( ph -> B e. C )
  assume constcncfg.c: |- ( ph -> C C_ CC )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> B ) e. ( A -cn-> C ) )

  proof
    wph
    cB
    cC
    wcel
    cA
    cc
    wss
    cC
    cc
    wss
    vx
    cA
    cB
    cmpt
    cA
    cC
    ccncf
    co
    wcel
    constcncfg.b
    constcncfg.a
    constcncfg.c
    vx
    cB
    cA
    cC
    cncfmptc
    syl3anc
end
