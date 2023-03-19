include "wss.mm"
include "cin.mm"
include "ssinss1.mm"
include "syl.mm"

theorem ssinss1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssinss1d.1: |- ( ph -> A C_ C )


  assert |- ( ph -> ( A i^i B ) C_ C )

  proof
    wph
    cA
    cC
    wss
    cA
    cB
    cin
    cC
    wss
    ssinss1d.1
    cA
    cB
    cC
    ssinss1
    syl
end
