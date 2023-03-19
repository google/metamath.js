include "wss.mm"
include "cdif.mm"
include "sscon.mm"
include "syl.mm"

theorem sscond
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssdifd.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( C \ B ) C_ ( C \ A ) )

  proof
    wph
    cA
    cB
    wss
    cC
    cB
    cdif
    cC
    cA
    cdif
    wss
    ssdifd.1
    cA
    cB
    cC
    sscon
    syl
end
