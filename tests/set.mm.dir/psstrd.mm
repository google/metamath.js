include "wpss.mm"
include "psstr.mm"
include "syl2anc.mm"

theorem psstrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume psstrd.1: |- ( ph -> A C. B )
  assume psstrd.2: |- ( ph -> B C. C )


  assert |- ( ph -> A C. C )

  proof
    wph
    cA
    cB
    wpss
    cB
    cC
    wpss
    cA
    cC
    wpss
    psstrd.1
    psstrd.2
    cA
    cB
    cC
    psstr
    syl2anc
end
