include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "ccxp.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "cxpexpz.mm"
include "syl3anc.mm"

theorem cxpexpzd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpexpzd.3: |- ( ph -> B e. ZZ )


  assert |- ( ph -> ( A ^c B ) = ( A ^ B ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cz
    wcel
    cA
    cB
    ccxp
    co
    cA
    cB
    cexp
    co
    wceq
    cxp0d.1
    cxpefd.2
    cxpexpzd.3
    cA
    cB
    cxpexpz
    syl3anc
end
