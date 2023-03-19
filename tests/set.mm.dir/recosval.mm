include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "ccj.mm"
include "ccos.mm"
include "cre.mm"
include "cc.mm"
include "wceq.mm"
include "ax-icn.mm"
include "recn.mm"
include "cjmul.mm"
include "sylancr.mm"
include "cji.mm"
include "oveq1i.mm"
include "cjre.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "mulcl.mm"
include "efcj.mm"
include "syl.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "cosval.mm"
include "efcl.mm"
include "reval.mm"
include "3syl.mm"
include "3eqtr4d.mm"

theorem recosval
  let cA: class A


  assert |- ( A e. RR -> ( cos ` A ) = ( Re ` ( exp ` ( _i x. A ) ) ) )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    cA
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @2
    @2
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    ccos
    cfv
    #
    @2
    cre
    cfv
    #
    @0
    @6
    @9
    c2
    cdiv
    @0
    @5
    @8
    @2
    caddc
    @0
    @1
    ccj
    cfv
    #
    ce
    cfv
    #
    @5
    @8
    @0
    @13
    @4
    ce
    @0
    @13
    ci
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    @4
    @0
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @13
    @17
    wceq
    ax-icn
    cA
    recn
    #
    ci
    cA
    cjmul
    sylancr
    @0
    @17
    @3
    @16
    cmul
    co
    @4
    @15
    @3
    @16
    cmul
    cji
    oveq1i
    @0
    @16
    cA
    @3
    cmul
    cA
    cjre
    oveq2d
    syl5eq
    eqtrd
    fveq2d
    @0
    @1
    cc
    wcel
    #
    @14
    @8
    wceq
    @0
    @18
    @19
    @21
    ax-icn
    @20
    ci
    cA
    mulcl
    sylancr
    #
    @1
    efcj
    syl
    eqtr3d
    oveq2d
    oveq1d
    @0
    @19
    @11
    @7
    wceq
    @20
    cA
    cosval
    syl
    @0
    @21
    @2
    cc
    wcel
    @12
    @10
    wceq
    @22
    @1
    efcl
    @2
    reval
    3syl
    3eqtr4d
end
