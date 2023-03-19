include "undmrnresiss.mm"

theorem reflexg
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( _I |` ( dom A u. ran A ) ) C_ A <-> A. x A. y ( x A y -> ( x A x /\ y A y ) ) )

  proof
    vx
    vy
    cA
    cA
    undmrnresiss
end
