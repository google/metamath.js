include "wcel.mm"
include "sseld.mm"
include "mpd.mm"

theorem sseldd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseld.1: |- ( ph -> A C_ B )
  assume sseldd.2: |- ( ph -> C e. A )


  assert |- ( ph -> C e. B )

  proof
    wph
    cC
    cA
    wcel
    cC
    cB
    wcel
    sseldd.2
    wph
    cA
    cB
    cC
    sseld.1
    sseld
    mpd
end
