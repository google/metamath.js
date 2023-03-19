include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wss.mm"
include "wcel.mm"
include "wbr.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "syl6breqr.mm"

theorem supxrubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  assume supxrubd.1: |- ( ph -> A C_ RR* )
  assume supxrubd.2: |- ( ph -> B e. A )
  assume supxrubd.3: |- S = sup ( A , RR* , < )


  assert |- ( ph -> B <_ S )

  proof
    wph
    cB
    cA
    cxr
    clt
    csup
    #
    cS
    cle
    wph
    cA
    cxr
    wss
    cB
    cA
    wcel
    cB
    @0
    cle
    wbr
    supxrubd.1
    supxrubd.2
    cA
    cB
    supxrub
    syl2anc
    supxrubd.3
    syl6breqr
end
