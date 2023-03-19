include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc.mm"
include "cmul.mm"
include "co.mm"
include "ccxp.mm"
include "wceq.mm"
include "cxpmul.mm"
include "syl3anc.mm"

theorem cxpmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume rpcxpcld.1: |- ( ph -> A e. RR+ )
  assume rpcxpcld.2: |- ( ph -> B e. RR )
  assume cxpmuld.4: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A ^c ( B x. C ) ) = ( ( A ^c B ) ^c C ) )

  proof
    wph
    cA
    crp
    wcel
    cB
    cr
    wcel
    cC
    cc
    wcel
    cA
    cB
    cC
    cmul
    co
    ccxp
    co
    cA
    cB
    ccxp
    co
    cC
    ccxp
    co
    wceq
    rpcxpcld.1
    rpcxpcld.2
    cxpmuld.4
    cA
    cB
    cC
    cxpmul
    syl3anc
end
