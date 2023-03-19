include "wss.mm"
include "wpss.mm"
include "sspsstr.mm"
include "syl2anc.mm"

theorem sspsstrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sspsstrd.1: |- ( ph -> A C_ B )
  assume sspsstrd.2: |- ( ph -> B C. C )


  assert |- ( ph -> A C. C )

  proof
    wph
    cA
    cB
    wss
    cB
    cC
    wpss
    cA
    cC
    wpss
    sspsstrd.1
    sspsstrd.2
    cA
    cB
    cC
    sspsstr
    syl2anc
end
