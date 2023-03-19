include "cxr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "xreqle.mm"
include "syl2anc.mm"

theorem xreqled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xreqled.1: |- ( ph -> A e. RR* )
  assume xreqled.2: |- ( ph -> A = B )


  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cB
    wceq
    cA
    cB
    cle
    wbr
    xreqled.1
    xreqled.2
    cA
    cB
    xreqle
    syl2anc
end
