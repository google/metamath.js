include "wf.mm"
include "feq1d.mm"
include "feq2d.mm"
include "bitrd.mm"

theorem feq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume feq12d.1: |- ( ph -> F = G )
  assume feq12d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( F : A --> C <-> G : B --> C ) )

  proof
    wph
    cA
    cC
    cF
    wf
    cA
    cC
    cG
    wf
    cB
    cC
    cG
    wf
    wph
    cA
    cC
    cF
    cG
    feq12d.1
    feq1d
    wph
    cA
    cB
    cC
    cG
    feq12d.2
    feq2d
    bitrd
end
