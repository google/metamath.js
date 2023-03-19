include "wss.mm"
include "cdif.mm"
include "ssdifss.mm"
include "syl.mm"

theorem ssdifssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssdifd.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( A \ C ) C_ B )

  proof
    wph
    cA
    cB
    wss
    cA
    cC
    cdif
    cB
    wss
    ssdifd.1
    cA
    cB
    cC
    ssdifss
    syl
end
