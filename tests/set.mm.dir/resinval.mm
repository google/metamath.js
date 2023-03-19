include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "ccj.mm"
include "csin.mm"
include "cim.mm"
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
include "sinval.mm"
include "efcl.mm"
include "imval2.mm"
include "3syl.mm"
include "3eqtr4d.mm"

theorem resinval
  let cA: class A


  assert |- ( A e. RR -> ( sin ` A ) = ( Im ` ( exp ` ( _i x. A ) ) ) )

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
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    @2
    @2
    ccj
    cfv
    #
    cmin
    co
    #
    @7
    cdiv
    co
    #
    cA
    csin
    cfv
    #
    @2
    cim
    cfv
    #
    @0
    @6
    @10
    @7
    cdiv
    @0
    @5
    @9
    @2
    cmin
    @0
    @1
    ccj
    cfv
    #
    ce
    cfv
    #
    @5
    @9
    @0
    @14
    @4
    ce
    @0
    @14
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
    @14
    @18
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
    @18
    @3
    @17
    cmul
    co
    @4
    @16
    @3
    @17
    cmul
    cji
    oveq1i
    @0
    @17
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
    @15
    @9
    wceq
    @0
    @19
    @20
    @22
    ax-icn
    @21
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
    @20
    @12
    @8
    wceq
    @21
    cA
    sinval
    syl
    @0
    @22
    @2
    cc
    wcel
    @13
    @11
    wceq
    @23
    @1
    efcl
    @2
    imval2
    3syl
    3eqtr4d
end
