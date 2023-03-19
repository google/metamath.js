include "cfn.mm"
include "hashss.mm"

theorem hashssle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B C_ A ) -> ( # ` B ) <_ ( # ` A ) )

  proof
    cA
    cB
    cfn
    hashss
end
