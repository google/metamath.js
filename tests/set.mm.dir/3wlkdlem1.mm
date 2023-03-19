include "chash.mm"
include "cfv.mm"
include "cs4.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2i.mm"
include "c3.mm"
include "c4.mm"
include "s4len.mm"
include "df-4.mm"
include "eqtri.mm"
include "cs3.mm"
include "s3len.mm"
include "eqtr2i.mm"
include "oveq1i.mm"

theorem 3wlkdlem1
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


  assert |- ( # ` P ) = ( ( # ` F ) + 1 )

  proof
    cP
    chash
    cfv
    cA
    cB
    cC
    cD
    cs4
    #
    chash
    cfv
    #
    cF
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cP
    @0
    chash
    3wlkd.p
    fveq2i
    @1
    c3
    c1
    caddc
    co
    #
    @3
    @1
    c4
    @4
    cA
    cB
    cC
    cD
    s4len
    df-4
    eqtri
    c3
    @2
    c1
    caddc
    @2
    cJ
    cK
    cL
    cs3
    #
    chash
    cfv
    c3
    cF
    @5
    chash
    3wlkd.f
    fveq2i
    cJ
    cK
    cL
    s3len
    eqtr2i
    oveq1i
    eqtri
    eqtri
end
