include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cmul.mm"
include "co.mm"
include "ccxp.mm"
include "cexp.mm"
include "wceq.mm"
include "cxpmul2.mm"
include "syl3anc.mm"

theorem cxpmul2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpcld.2: |- ( ph -> B e. CC )
  assume cxpmul2d.4: |- ( ph -> C e. NN0 )


  assert |- ( ph -> ( A ^c ( B x. C ) ) = ( ( A ^c B ) ^ C ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cn0
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
    cexp
    co
    wceq
    cxp0d.1
    cxpcld.2
    cxpmul2d.4
    cA
    cB
    cC
    cxpmul2
    syl3anc
end
