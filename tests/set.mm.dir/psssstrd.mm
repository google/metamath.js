include "wpss.mm"
include "wss.mm"
include "psssstr.mm"
include "syl2anc.mm"

theorem psssstrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume psssstrd.1: |- ( ph -> A C. B )
  assume psssstrd.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C. C )

  proof
    wph
    cA
    cB
    wpss
    cB
    cC
    wss
    cA
    cC
    wpss
    psssstrd.1
    psssstrd.2
    cA
    cB
    cC
    psssstr
    syl2anc
end
