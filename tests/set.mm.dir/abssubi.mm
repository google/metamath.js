include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "abssub.mm"
include "mp2an.mm"

theorem abssubi
  let cA: class A
  let cB: class B
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC


  assert |- ( abs ` ( A - B ) ) = ( abs ` ( B - A ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmin
    co
    cabs
    cfv
    cB
    cA
    cmin
    co
    cabs
    cfv
    wceq
    absvalsqi.1
    abssub.2
    cA
    cB
    abssub
    mp2an
end
