include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "ccnfld.mm"
include "cress.mm"
include "csg.mm"
include "cfv.mm"
include "csubg.mm"
include "wceq.mm"
include "csubrg.mm"
include "clmsubrg.mm"
include "subrgsubg.mm"
include "syl.mm"
include "cnfldsub.mm"
include "eqid.mm"
include "subgsub.mm"
include "syl3an1.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "eqtr4d.mm"

theorem clmsub
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ A e. K /\ B e. K ) -> ( A - B ) = ( A ( -g ` F ) B ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cK
    wcel
    #
    w3a
    #
    cA
    cB
    cmin
    co
    #
    cA
    cB
    ccnfld
    cK
    cress
    co
    #
    csg
    cfv
    #
    co
    #
    cA
    cB
    cF
    csg
    cfv
    #
    co
    @0
    cK
    ccnfld
    csubg
    cfv
    wcel
    #
    @1
    @2
    @4
    @7
    wceq
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @9
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsubrg
    cK
    ccnfld
    subrgsubg
    syl
    cK
    ccnfld
    @5
    cmin
    @6
    cA
    cB
    cnfldsub
    @5
    eqid
    @6
    eqid
    subgsub
    syl3an1
    @3
    @8
    @6
    cA
    cB
    @0
    @1
    @8
    @6
    wceq
    @2
    @0
    cF
    @5
    csg
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsca
    fveq2d
    3ad2ant1
    oveqd
    eqtr4d
end
