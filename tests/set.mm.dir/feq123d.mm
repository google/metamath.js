include "wf.mm"
include "feq12d.mm"
include "feq3d.mm"
include "bitrd.mm"

theorem feq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume feq12d.1: |- ( ph -> F = G )
  assume feq12d.2: |- ( ph -> A = B )
  assume feq123d.3: |- ( ph -> C = D )


  assert |- ( ph -> ( F : A --> C <-> G : B --> D ) )

  proof
    wph
    cA
    cC
    cF
    wf
    cB
    cC
    cG
    wf
    cB
    cD
    cG
    wf
    wph
    cA
    cB
    cC
    cF
    cG
    feq12d.1
    feq12d.2
    feq12d
    wph
    cC
    cD
    cG
    cB
    feq123d.3
    feq3d
    bitrd
end
