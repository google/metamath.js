include "wss.mm"
include "a1i.mm"
include "sstrd.mm"

theorem syl5ss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5ss.1: |- A C_ B
  assume syl5ss.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    cA
    cB
    wss
    wph
    syl5ss.1
    a1i
    syl5ss.2
    sstrd
end
