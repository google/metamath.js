include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "ccxp.mm"
include "co.mm"
include "wb.mm"
include "cxple.mm"
include "syl22anc.mm"

theorem cxpled
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume cxpltd.2: |- ( ph -> 1 < A )
  assume cxpltd.3: |- ( ph -> B e. RR )
  assume cxpltd.4: |- ( ph -> C e. RR )


  assert |- ( ph -> ( B <_ C <-> ( A ^c B ) <_ ( A ^c C ) ) )

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
    cle
    wbr
    cA
    cB
    ccxp
    co
    cA
    cC
    ccxp
    co
    cle
    wbr
    wb
    recxpcld.1
    cxpltd.2
    cxpltd.3
    cxpltd.4
    cA
    cB
    cC
    cxple
    syl22anc
end
