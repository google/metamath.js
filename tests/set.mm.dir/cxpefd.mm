include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "wceq.mm"
include "cxpef.mm"
include "syl3anc.mm"

theorem cxpefd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxp0d.1: |- ( ph -> A e. CC )
  assume cxpefd.2: |- ( ph -> A =/= 0 )
  assume cxpefd.3: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A ^c B ) = ( exp ` ( B x. ( log ` A ) ) ) )

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
    cB
    cA
    clog
    cfv
    cmul
    co
    ce
    cfv
    wceq
    cxp0d.1
    cxpefd.2
    cxpefd.3
    cA
    cB
    cxpef
    syl3anc
end
