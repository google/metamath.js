include "chil.mm"
include "cch.mm"
include "helch.mm"
include "elimel.mm"

theorem ifchhv
  let cA: class A


  assert |- if ( A e. CH , A , ~H ) e. CH

  proof
    cA
    chil
    cch
    helch
    elimel
end
