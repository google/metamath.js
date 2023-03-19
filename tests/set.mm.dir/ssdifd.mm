include "wss.mm"
include "cdif.mm"
include "ssdif.mm"
include "syl.mm"

theorem ssdifd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssdifd.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( A \ C ) C_ ( B \ C ) )

  proof
    wph
    cA
    cB
    wss
    cA
    cC
    cdif
    cB
    cC
    cdif
    wss
    ssdifd.1
    cA
    cB
    cC
    ssdif
    syl
end
