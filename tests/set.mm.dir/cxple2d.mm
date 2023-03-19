include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "ccxp.mm"
include "co.mm"
include "wb.mm"
include "cxple2.mm"
include "syl221anc.mm"

theorem cxple2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume recxpcld.2: |- ( ph -> 0 <_ A )
  assume recxpcld.3: |- ( ph -> B e. RR )
  assume mulcxpd.4: |- ( ph -> 0 <_ B )
  assume cxple2d.5: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( A <_ B <-> ( A ^c C ) <_ ( B ^c C ) ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cC
    crp
    wcel
    cA
    cB
    cle
    wbr
    cA
    cC
    ccxp
    co
    cB
    cC
    ccxp
    co
    cle
    wbr
    wb
    recxpcld.1
    recxpcld.2
    recxpcld.3
    mulcxpd.4
    cxple2d.5
    cA
    cB
    cC
    cxple2
    syl221anc
end
