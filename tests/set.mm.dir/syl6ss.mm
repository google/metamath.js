include "wss.mm"
include "a1i.mm"
include "sstrd.mm"

theorem syl6ss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6ss.1: |- ( ph -> A C_ B )
  assume syl6ss.2: |- B C_ C


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    syl6ss.1
    cB
    cC
    wss
    wph
    syl6ss.2
    a1i
    sstrd
end
