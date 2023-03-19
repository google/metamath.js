include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absmul.mm"
include "mp2an.mm"

theorem absmuli
  let cA: class A
  let cB: class B
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC


  assert |- ( abs ` ( A x. B ) ) = ( ( abs ` A ) x. ( abs ` B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cabs
    cfv
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    cmul
    co
    wceq
    absvalsqi.1
    abssub.2
    cA
    cB
    absmul
    mp2an
end
