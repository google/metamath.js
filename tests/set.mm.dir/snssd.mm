include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "snssi.mm"
include "syl.mm"

theorem snssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume snssd.1: |- ( ph -> A e. B )


  assert |- ( ph -> { A } C_ B )

  proof
    wph
    cA
    cB
    wcel
    cA
    csn
    cB
    wss
    snssd.1
    cA
    cB
    snssi
    syl
end
