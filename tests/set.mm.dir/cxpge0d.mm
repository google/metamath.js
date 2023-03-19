include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "cxpge0.mm"
include "syl3anc.mm"

theorem cxpge0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume recxpcld.2: |- ( ph -> 0 <_ A )
  assume recxpcld.3: |- ( ph -> B e. RR )


  assert |- ( ph -> 0 <_ ( A ^c B ) )

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
    cA
    cB
    ccxp
    co
    cle
    wbr
    recxpcld.1
    recxpcld.2
    recxpcld.3
    cA
    cB
    cxpge0
    syl3anc
end
