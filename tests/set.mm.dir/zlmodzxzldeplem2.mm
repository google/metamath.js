include "cz.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "zlmodzxzldeplem1.mm"
include "cvv.mm"
include "elmapi.mm"
include "cfn.mm"
include "prfi.mm"
include "a1i.mm"
include "c0ex.mm"
include "fdmfifsupp.mm"
include "ax-mp.mm"

theorem zlmodzxzldeplem2
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }
  assume zlmodzxzldeplem.f: |- F = { <. A , 2 >. , <. B , -u 3 >. }


  assert |- F finSupp 0

  proof
    cF
    cz
    cA
    cB
    cpr
    #
    cmap
    co
    wcel
    #
    cF
    cc0
    cfsupp
    wbr
    cA
    cB
    cF
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    zlmodzxzldeplem.f
    zlmodzxzldeplem1
    @1
    @0
    cz
    cF
    cvv
    cc0
    cF
    cz
    @0
    elmapi
    @0
    cfn
    wcel
    @1
    cA
    cB
    prfi
    a1i
    cc0
    cvv
    wcel
    @1
    c0ex
    a1i
    fdmfifsupp
    ax-mp
end
