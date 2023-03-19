include "ax-mulass.mm"

theorem mulass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A x. B ) x. C ) = ( A x. ( B x. C ) ) )

  proof
    cA
    cB
    cC
    ax-mulass
end
