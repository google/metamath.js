include "wss.mm"
include "sstr.mm"
include "syl2anc.mm"

theorem sstrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sstrd.1: |- ( ph -> A C_ B )
  assume sstrd.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    wss
    cB
    cC
    wss
    cA
    cC
    wss
    sstrd.1
    sstrd.2
    cA
    cB
    cC
    sstr
    syl2anc
end
