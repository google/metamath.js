include "chash.mm"
include "cfv.mm"
include "cs3.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2i.mm"
include "c2.mm"
include "c3.mm"
include "s3len.mm"
include "df-3.mm"
include "eqtri.mm"
include "cs2.mm"
include "s2len.mm"
include "eqtr2i.mm"
include "oveq1i.mm"

theorem 2wlkdlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">


  assert |- ( # ` P ) = ( ( # ` F ) + 1 )

  proof
    cP
    chash
    cfv
    cA
    cB
    cC
    cs3
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
    2wlkd.p
    fveq2i
    @1
    c2
    c1
    caddc
    co
    #
    @3
    @1
    c3
    @4
    cA
    cB
    cC
    s3len
    df-3
    eqtri
    c2
    @2
    c1
    caddc
    @2
    cJ
    cK
    cs2
    #
    chash
    cfv
    c2
    cF
    @5
    chash
    2wlkd.f
    fveq2i
    cJ
    cK
    s2len
    eqtr2i
    oveq1i
    eqtri
    eqtri
end
