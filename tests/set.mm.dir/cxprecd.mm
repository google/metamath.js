include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "wceq.mm"
include "cxprec.mm"
include "syl2anc.mm"

theorem cxprecd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpcxpcld.1: |- ( ph -> A e. RR+ )
  assume cxprecd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( 1 / A ) ^c B ) = ( 1 / ( A ^c B ) ) )

  proof
    wph
    cA
    crp
    wcel
    cB
    cc
    wcel
    c1
    cA
    cdiv
    co
    cB
    ccxp
    co
    c1
    cA
    cB
    ccxp
    co
    cdiv
    co
    wceq
    rpcxpcld.1
    cxprecd.2
    cA
    cB
    cxprec
    syl2anc
end
