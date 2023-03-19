include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "c3.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "cs3.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo0to3tp.mm"

theorem 3wlkdlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">


  assert |- ( 0 ..^ ( # ` F ) ) = { 0 , 1 , 2 }

  proof
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    cc0
    c3
    cfzo
    co
    cc0
    c1
    c2
    ctp
    @0
    c3
    cc0
    cfzo
    @0
    cJ
    cK
    cL
    cs3
    #
    chash
    cfv
    c3
    cF
    @1
    chash
    3wlkd.f
    fveq2i
    cJ
    cK
    cL
    s3len
    eqtri
    oveq2i
    fzo0to3tp
    eqtri
end
