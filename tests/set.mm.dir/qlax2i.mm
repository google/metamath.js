include "chjcomi.mm"

theorem qlax2i
  let cA: class A
  let cB: class B
  assume qlax.1: |- A e. CH
  assume qlax.2: |- B e. CH


  assert |- ( A vH B ) = ( B vH A )

  proof
    cA
    cB
    qlax.1
    qlax.2
    chjcomi
end
