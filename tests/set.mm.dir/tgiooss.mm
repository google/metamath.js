include "rerest.mm"

theorem tgiooss
  let cA: class A
  let cJ: class J
  let cK: class K
  assume tgiooss.1: |- J = ( TopOpen ` CCfld )
  assume tgiooss.2: |- K = ( topGen ` ran (,) )


  assert |- ( A C_ RR -> ( J |`t A ) = ( K |`t A ) )

  proof
    cA
    cK
    cJ
    tgiooss.1
    tgiooss.2
    rerest
end
