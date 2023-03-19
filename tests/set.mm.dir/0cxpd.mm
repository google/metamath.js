include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "0cxp.mm"
include "syl2anc.mm"

theorem 0cxpd
  let wph: wff ph
  let cA: class A
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( 0 ^c A ) = 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cc0
    cA
    ccxp
    co
    cc0
    wceq
    cxp0d.1
    cxpefd.2
    cA
    0cxp
    syl2anc
end
