include "wss.mm"
include "cc.mm"
include "cv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cncfmptid.mm"
include "syl2anc.mm"

theorem idcncfg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume idcncfg.a: |- ( ph -> A C_ B )
  assume idcncfg.b: |- ( ph -> B C_ CC )

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> x ) e. ( A -cn-> B ) )

  proof
    wph
    cA
    cB
    wss
    cB
    cc
    wss
    vx
    cA
    vx
    cv
    cmpt
    cA
    cB
    ccncf
    co
    wcel
    idcncfg.a
    idcncfg.b
    vx
    cA
    cB
    cncfmptid
    syl2anc
end
