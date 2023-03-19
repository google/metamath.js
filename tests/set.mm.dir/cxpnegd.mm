include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cneg.mm"
include "ccxp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "wceq.mm"
include "cxpneg.mm"
include "syl3anc.mm"

theorem cxpnegd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpefd.3: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A ^c -u B ) = ( 1 / ( A ^c B ) ) )

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
    cneg
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
    cxp0d.1
    cxpefd.2
    cxpefd.3
    cA
    cB
    cxpneg
    syl3anc
end
