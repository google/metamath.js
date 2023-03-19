include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c1.mm"
include "ci.mm"
include "cneg.mm"
include "caddc.mm"
include "wi.mm"
include "ax-1cn.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "negicn.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "cim.mm"
include "replim.mm"
include "mulid2.mm"
include "eqcomd.mm"
include "imre.mm"
include "eqtrd.mm"
include "eqeqan12d.mm"
include "syl5ibr.mm"
include "oveq2.mm"
include "ralrimivw.mm"
include "impbid1.mm"

theorem recan
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A. x e. CC ( Re ` ( x x. A ) ) = ( Re ` ( x x. B ) ) <-> A = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    cmul
    co
    #
    cre
    cfv
    #
    @3
    cB
    cmul
    co
    #
    cre
    cfv
    #
    wceq
    #
    vx
    cc
    wral
    #
    cA
    cB
    wceq
    #
    @9
    @10
    @2
    c1
    cA
    cmul
    co
    #
    cre
    cfv
    #
    ci
    ci
    cneg
    #
    cA
    cmul
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    c1
    cB
    cmul
    co
    #
    cre
    cfv
    #
    ci
    @13
    cB
    cmul
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @9
    @12
    @19
    @16
    @22
    caddc
    c1
    cc
    wcel
    @9
    @12
    @19
    wceq
    #
    wi
    ax-1cn
    @8
    @24
    vx
    c1
    cc
    @3
    c1
    wceq
    #
    @5
    @12
    @7
    @19
    @25
    @4
    @11
    cre
    @3
    c1
    cA
    cmul
    oveq1
    fveq2d
    @25
    @6
    @18
    cre
    @3
    c1
    cB
    cmul
    oveq1
    fveq2d
    eqeq12d
    rspcv
    ax-mp
    @9
    @15
    @21
    ci
    cmul
    @13
    cc
    wcel
    @9
    @15
    @21
    wceq
    #
    wi
    negicn
    @8
    @26
    vx
    @13
    cc
    @3
    @13
    wceq
    #
    @5
    @15
    @7
    @21
    @27
    @4
    @14
    cre
    @3
    @13
    cA
    cmul
    oveq1
    fveq2d
    @27
    @6
    @20
    cre
    @3
    @13
    cB
    cmul
    oveq1
    fveq2d
    eqeq12d
    rspcv
    ax-mp
    oveq2d
    oveq12d
    @0
    @1
    cA
    @17
    cB
    @23
    @0
    cA
    cA
    cre
    cfv
    #
    ci
    cA
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @17
    cA
    replim
    @0
    @28
    @12
    @30
    @16
    caddc
    @0
    cA
    @11
    cre
    @0
    @11
    cA
    cA
    mulid2
    eqcomd
    fveq2d
    @0
    @29
    @15
    ci
    cmul
    cA
    imre
    oveq2d
    oveq12d
    eqtrd
    @1
    cB
    cB
    cre
    cfv
    #
    ci
    cB
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @23
    cB
    replim
    @1
    @31
    @19
    @33
    @22
    caddc
    @1
    cB
    @18
    cre
    @1
    @18
    cB
    cB
    mulid2
    eqcomd
    fveq2d
    @1
    @32
    @21
    ci
    cmul
    cB
    imre
    oveq2d
    oveq12d
    eqtrd
    eqeqan12d
    syl5ibr
    @10
    @8
    vx
    cc
    @10
    @4
    @6
    cre
    cA
    cB
    @3
    cmul
    oveq2
    fveq2d
    ralrimivw
    impbid1
end
