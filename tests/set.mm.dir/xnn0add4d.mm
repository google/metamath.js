include "cxnn0.mm"
include "wcel.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "xnn0xrnemnf.mm"
include "syl.mm"
include "xadd4d.mm"

theorem xnn0add4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xnn0add4d.1: |- ( ph -> A e. NN0* )
  assume xnn0add4d.2: |- ( ph -> B e. NN0* )
  assume xnn0add4d.3: |- ( ph -> C e. NN0* )
  assume xnn0add4d.4: |- ( ph -> D e. NN0* )


  assert |- ( ph -> ( ( A +e B ) +e ( C +e D ) ) = ( ( A +e C ) +e ( B +e D ) ) )

  proof
    wph
    cA
    cB
    cC
    cD
    wph
    cA
    cxnn0
    wcel
    cA
    cxr
    wcel
    cA
    cmnf
    wne
    wa
    xnn0add4d.1
    cA
    xnn0xrnemnf
    syl
    wph
    cB
    cxnn0
    wcel
    cB
    cxr
    wcel
    cB
    cmnf
    wne
    wa
    xnn0add4d.2
    cB
    xnn0xrnemnf
    syl
    wph
    cC
    cxnn0
    wcel
    cC
    cxr
    wcel
    cC
    cmnf
    wne
    wa
    xnn0add4d.3
    cC
    xnn0xrnemnf
    syl
    wph
    cD
    cxnn0
    wcel
    cD
    cxr
    wcel
    cD
    cmnf
    wne
    wa
    xnn0add4d.4
    cD
    xnn0xrnemnf
    syl
    xadd4d
end
