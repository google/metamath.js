include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "wb.mm"
include "cxplt.mm"
include "syl22anc.mm"

theorem cxpltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume cxpltd.2: |- ( ph -> 1 < A )
  assume cxpltd.3: |- ( ph -> B e. RR )
  assume cxpltd.4: |- ( ph -> C e. RR )


  assert |- ( ph -> ( B < C <-> ( A ^c B ) < ( A ^c C ) ) )

  proof
    wph
    cA
    cr
    wcel
    c1
    cA
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
    cB
    ccxp
    co
    cA
    cC
    ccxp
    co
    clt
    wbr
    wb
    recxpcld.1
    cxpltd.2
    cxpltd.3
    cxpltd.4
    cA
    cB
    cC
    cxplt
    syl22anc
end
