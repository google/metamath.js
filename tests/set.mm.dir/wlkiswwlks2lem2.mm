include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "ccnv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "adantl.mm"
include "simpr.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem wlkiswwlks2lem2
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cI: class I
  assume wlkiswwlks2lem.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) )

  disjoint P x
  disjoint E x
  disjoint I x
  assert |- ( ( ( # ` P ) e. NN0 /\ I e. ( 0 ..^ ( ( # ` P ) - 1 ) ) ) -> ( F ` I ) = ( `' E ` { ( P ` I ) , ( P ` ( I + 1 ) ) } ) )

  proof
    cP
    chash
    cfv
    #
    cn0
    wcel
    #
    cI
    cc0
    @0
    c1
    cmin
    co
    cfzo
    co
    #
    wcel
    #
    wa
    #
    vx
    cI
    vx
    cv
    #
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    ccnv
    #
    cfv
    #
    cI
    cP
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @10
    cfv
    #
    @2
    cF
    cvv
    cF
    vx
    @2
    @11
    cmpt
    wceq
    @4
    wlkiswwlks2lem.f
    a1i
    @5
    cI
    wceq
    #
    @11
    @16
    wceq
    @4
    @17
    @9
    @15
    @10
    @17
    @6
    @12
    @8
    @14
    @5
    cI
    cP
    fveq2
    @17
    @7
    @13
    cP
    @5
    cI
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    fveq2d
    adantl
    @1
    @3
    simpr
    @4
    @15
    @10
    fvexd
    fvmptd
end
