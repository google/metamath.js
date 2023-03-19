include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "abs2dif.mm"
include "mp2an.mm"

theorem abs2difi
  let cA: class A
  let cB: class B
  assume abs2difi.1: |- A e. CC
  assume abs2difi.2: |- B e. CC


  assert |- ( ( abs ` A ) - ( abs ` B ) ) <_ ( abs ` ( A - B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    cmin
    co
    cA
    cB
    cmin
    co
    cabs
    cfv
    cle
    wbr
    abs2difi.1
    abs2difi.2
    cA
    cB
    abs2dif
    mp2an
end
