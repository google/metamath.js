include "wcel.mm"
include "wn.mm"
include "wpss.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "ssnelpss.mm"
include "syl.mm"
include "mp2and.mm"

theorem ssnelpssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssnelpssd.1: |- ( ph -> A C_ B )
  assume ssnelpssd.2: |- ( ph -> C e. B )
  assume ssnelpssd.3: |- ( ph -> -. C e. A )


  assert |- ( ph -> A C. B )

  proof
    wph
    cC
    cB
    wcel
    #
    cC
    cA
    wcel
    wn
    #
    cA
    cB
    wpss
    #
    ssnelpssd.2
    ssnelpssd.3
    wph
    cA
    cB
    wss
    @0
    @1
    wa
    @2
    wi
    ssnelpssd.1
    cA
    cB
    cC
    ssnelpss
    syl
    mp2and
end
