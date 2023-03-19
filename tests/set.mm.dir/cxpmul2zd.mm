include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cmul.mm"
include "co.mm"
include "ccxp.mm"
include "cexp.mm"
include "wceq.mm"
include "cxpmul2z.mm"
include "syl22anc.mm"

theorem cxpmul2zd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpefd.3: |- ( ph -> B e. CC )
  assume cxpmul2zd.4: |- ( ph -> C e. ZZ )


  assert |- ( ph -> ( A ^c ( B x. C ) ) = ( ( A ^c B ) ^ C ) )

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
    cz
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
    cxpefd.2
    cxpefd.3
    cxpmul2zd.4
    cA
    cB
    cC
    cxpmul2z
    syl22anc
end
