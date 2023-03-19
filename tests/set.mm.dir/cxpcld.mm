include "cc.mm"
include "wcel.mm"
include "ccxp.mm"
include "co.mm"
include "cxpcl.mm"
include "syl2anc.mm"

theorem cxpcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpcld.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A ^c B ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    ccxp
    co
    cc
    wcel
    cxp0d.1
    cxpcld.2
    cA
    cB
    cxpcl
    syl2anc
end
