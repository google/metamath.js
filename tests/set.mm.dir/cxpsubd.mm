include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "ccxp.mm"
include "cdiv.mm"
include "wceq.mm"
include "cxpsub.mm"
include "syl211anc.mm"

theorem cxpsubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpefd.3: |- ( ph -> B e. CC )
  assume cxpaddd.4: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A ^c ( B - C ) ) = ( ( A ^c B ) / ( A ^c C ) ) )

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
    cC
    cc
    wcel
    cA
    cB
    cC
    cmin
    co
    ccxp
    co
    cA
    cB
    ccxp
    co
    cA
    cC
    ccxp
    co
    cdiv
    co
    wceq
    cxp0d.1
    cxpefd.2
    cxpefd.3
    cxpaddd.4
    cA
    cB
    cC
    cxpsub
    syl211anc
end
