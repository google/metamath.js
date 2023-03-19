include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "ccxp.mm"
include "co.mm"
include "wb.mm"
include "cxplt3.mm"
include "syl22anc.mm"

theorem cxplt3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume rpcxpcld.1: |- ( ph -> A e. RR+ )
  assume rpcxpcld.2: |- ( ph -> B e. RR )
  assume cxplt3d.3: |- ( ph -> A < 1 )
  assume cxplt3d.4: |- ( ph -> C e. RR )


  assert |- ( ph -> ( B < C <-> ( A ^c C ) < ( A ^c B ) ) )

  proof
    wph
    cA
    crp
    wcel
    cA
    c1
    clt
    wbr
    cB
    cr
    wcel
    cC
    cr
    wcel
    cB
    cC
    clt
    wbr
    cA
    cC
    ccxp
    co
    cA
    cB
    ccxp
    co
    clt
    wbr
    wb
    rpcxpcld.1
    cxplt3d.3
    rpcxpcld.2
    cxplt3d.4
    cA
    cB
    cC
    cxplt3
    syl22anc
end
