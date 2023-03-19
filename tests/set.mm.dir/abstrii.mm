include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "abstri.mm"
include "mp2an.mm"

theorem abstrii
  let cA: class A
  let cB: class B
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC


  assert |- ( abs ` ( A + B ) ) <_ ( ( abs ` A ) + ( abs ` B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cabs
    cfv
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    caddc
    co
    cle
    wbr
    absvalsqi.1
    abssub.2
    cA
    cB
    abstri
    mp2an
end
