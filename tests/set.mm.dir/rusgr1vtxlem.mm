include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c0.mm"
include "wa.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "wi.mm"
include "r19.26.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "biimpac.mm"
include "ralimi.mm"
include "wne.mm"
include "hash1n0.mm"
include "rspn0.mm"
include "syl.mm"
include "hash0.mm"
include "eqeq1.mm"
include "mpbii.mm"
include "syl6com.mm"
include "sylbir.mm"
include "imp.mm"

theorem rusgr1vtxlem
  let vv: setvar v
  let cA: class A
  let cK: class K
  let cV: class V
  let cW: class W

  disjoint K v
  disjoint V v
  assert |- ( ( ( A. v e. V ( # ` A ) = K /\ A. v e. V A = (/) ) /\ ( V e. W /\ ( # ` V ) = 1 ) ) -> K = 0 )

  proof
    cA
    chash
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    cA
    c0
    wceq
    #
    vv
    cV
    wral
    wa
    #
    cV
    cW
    wcel
    cV
    chash
    cfv
    c1
    wceq
    wa
    #
    cK
    cc0
    wceq
    #
    @3
    @1
    @2
    wa
    #
    vv
    cV
    wral
    #
    @4
    @5
    wi
    #
    @1
    @2
    vv
    cV
    r19.26
    @7
    c0
    chash
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    @8
    @6
    @10
    vv
    cV
    @2
    @1
    @10
    @2
    @0
    @9
    cK
    cA
    c0
    chash
    fveq2
    eqeq1d
    biimpac
    ralimi
    @4
    @11
    @10
    @5
    @4
    cV
    c0
    wne
    @11
    @10
    wi
    cV
    cW
    hash1n0
    @10
    vv
    cV
    rspn0
    syl
    @10
    @9
    cc0
    wceq
    @5
    hash0
    @9
    cK
    cc0
    eqeq1
    mpbii
    syl6com
    syl
    sylbir
    imp
end
