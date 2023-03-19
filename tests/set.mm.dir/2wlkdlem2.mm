include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "cpr.mm"
include "cs2.mm"
include "fveq2i.mm"
include "s2len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo0to2pr.mm"

theorem 2wlkdlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">


  assert |- ( 0 ..^ ( # ` F ) ) = { 0 , 1 }

  proof
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    cc0
    c2
    cfzo
    co
    cc0
    c1
    cpr
    @0
    c2
    cc0
    cfzo
    @0
    cJ
    cK
    cs2
    #
    chash
    cfv
    c2
    cF
    @1
    chash
    2wlkd.f
    fveq2i
    cJ
    cK
    s2len
    eqtri
    oveq2i
    fzo0to2pr
    eqtri
end
