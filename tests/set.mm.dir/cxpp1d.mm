include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ccxp.mm"
include "cmul.mm"
include "wceq.mm"
include "cxpp1.mm"
include "syl3anc.mm"

theorem cxpp1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpefd.3: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A ^c ( B + 1 ) ) = ( ( A ^c B ) x. A ) )

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
    c1
    caddc
    co
    ccxp
    co
    cA
    cB
    ccxp
    co
    cA
    cmul
    co
    wceq
    cxp0d.1
    cxpefd.2
    cxpefd.3
    cA
    cB
    cxpp1
    syl3anc
end
