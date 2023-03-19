include "wcel.mm"
include "wn.mm"
include "ssneld.mm"
include "mpd.mm"

theorem ssneldd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssneld.1: |- ( ph -> A C_ B )
  assume ssneldd.2: |- ( ph -> -. C e. B )


  assert |- ( ph -> -. C e. A )

  proof
    wph
    cC
    cB
    wcel
    wn
    cC
    cA
    wcel
    wn
    ssneldd.2
    wph
    cA
    cB
    cC
    ssneld.1
    ssneld
    mpd
end
