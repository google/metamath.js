include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "recxpcl.mm"
include "syl3anc.mm"

theorem recxpcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume recxpcld.2: |- ( ph -> 0 <_ A )
  assume recxpcld.3: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A ^c B ) e. RR )

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
    cA
    cB
    ccxp
    co
    cr
    wcel
    recxpcld.1
    recxpcld.2
    recxpcld.3
    cA
    cB
    recxpcl
    syl3anc
end
