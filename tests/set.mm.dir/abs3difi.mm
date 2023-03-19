include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "abs3dif.mm"
include "mp3an.mm"

theorem abs3difi
  let cA: class A
  let cB: class B
  let cC: class C
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC
  assume abs3dif.3: |- C e. CC


  assert |- ( abs ` ( A - B ) ) <_ ( ( abs ` ( A - C ) ) + ( abs ` ( C - B ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    cmin
    co
    cabs
    cfv
    cA
    cC
    cmin
    co
    cabs
    cfv
    cC
    cB
    cmin
    co
    cabs
    cfv
    caddc
    co
    cle
    wbr
    absvalsqi.1
    abssub.2
    abs3dif.3
    cA
    cB
    cC
    abs3dif
    mp3an
end
