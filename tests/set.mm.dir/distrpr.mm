include "cnp.mm"
include "wcel.mm"
include "w3a.mm"
include "cpp.mm"
include "co.mm"
include "cmp.mm"
include "wceq.mm"
include "distrlem1pr.mm"
include "distrlem5pr.mm"
include "eqssd.mm"
include "dmplp.mm"
include "0npr.mm"
include "dmmp.mm"
include "ndmovdistr.mm"
include "pm2.61i.mm"

theorem distrpr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A .P. ( B +P. C ) ) = ( ( A .P. B ) +P. ( A .P. C ) )

  proof
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    cC
    cnp
    wcel
    w3a
    #
    cA
    cB
    cC
    cpp
    co
    cmp
    co
    #
    cA
    cB
    cmp
    co
    cA
    cC
    cmp
    co
    cpp
    co
    #
    wceq
    @0
    @1
    @2
    cA
    cB
    cC
    distrlem1pr
    cA
    cB
    cC
    distrlem5pr
    eqssd
    cA
    cB
    cC
    cnp
    cpp
    cmp
    dmplp
    0npr
    dmmp
    ndmovdistr
    pm2.61i
end
