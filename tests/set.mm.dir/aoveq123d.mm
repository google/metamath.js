include "cop.mm"
include "cafv.mm"
include "caov.mm"
include "opeq12d.mm"
include "afveq12d.mm"
include "df-aov.mm"
include "3eqtr4g.mm"

theorem aoveq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume aoveq123d.1: |- ( ph -> F = G )
  assume aoveq123d.2: |- ( ph -> A = B )
  assume aoveq123d.3: |- ( ph -> C = D )


  assert |- ( ph -> (( A F C )) = (( B G D )) )

  proof
    wph
    cA
    cC
    cop
    #
    cF
    cafv
    cB
    cD
    cop
    #
    cG
    cafv
    cA
    cC
    cF
    caov
    cB
    cD
    cG
    caov
    wph
    @0
    @1
    cF
    cG
    aoveq123d.1
    wph
    cA
    cB
    cC
    cD
    aoveq123d.2
    aoveq123d.3
    opeq12d
    afveq12d
    cA
    cC
    cF
    df-aov
    cB
    cD
    cG
    df-aov
    3eqtr4g
end
