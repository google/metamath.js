include "caddc.mm"
include "oveq12d.mm"

theorem int-eqprincd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-eqprincd.1: |- ( ph -> A = B )
  assume int-eqprincd.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A + C ) = ( B + D ) )

  proof
    wph
    cA
    cB
    cC
    cD
    caddc
    int-eqprincd.1
    int-eqprincd.2
    oveq12d
end
