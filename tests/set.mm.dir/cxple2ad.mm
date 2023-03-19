include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "cxple2a.mm"
include "syl321anc.mm"

theorem cxple2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume recxpcld.2: |- ( ph -> 0 <_ A )
  assume recxpcld.3: |- ( ph -> B e. RR )
  assume cxple2ad.4: |- ( ph -> C e. RR )
  assume cxple2ad.5: |- ( ph -> 0 <_ C )
  assume cxple2ad.6: |- ( ph -> A <_ B )


  assert |- ( ph -> ( A ^c C ) <_ ( B ^c C ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cc0
    cC
    cle
    wbr
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
    recxpcld.1
    recxpcld.3
    cxple2ad.4
    recxpcld.2
    cxple2ad.5
    cxple2ad.6
    cA
    cB
    cC
    cxple2a
    syl321anc
end
