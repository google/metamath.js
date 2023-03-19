include "chjassi.mm"

theorem qlax3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume qlax.1: |- A e. CH
  assume qlax.2: |- B e. CH
  assume qlax.3: |- C e. CH


  assert |- ( ( A vH B ) vH C ) = ( A vH ( B vH C ) )

  proof
    cA
    cB
    cC
    qlax.1
    qlax.2
    qlax.3
    chjassi
end
