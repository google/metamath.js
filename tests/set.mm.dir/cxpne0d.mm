include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "ccxp.mm"
include "co.mm"
include "cxpne0.mm"
include "syl3anc.mm"

theorem cxpne0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpefd.3: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A ^c B ) =/= 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc
    wcel
    cA
    cB
    ccxp
    co
    cc0
    wne
    cxp0d.1
    cxpefd.2
    cxpefd.3
    cA
    cB
    cxpne0
    syl3anc
end
