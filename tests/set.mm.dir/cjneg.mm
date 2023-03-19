include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cre.mm"
include "cfv.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "ccj.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "neg2subd.mm"
include "reneg.mm"
include "imneg.mm"
include "oveq2d.mm"
include "wceq.mm"
include "mulneg2.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "negsubdi2d.mm"
include "3eqtr4d.mm"
include "negcl.mm"
include "remim.mm"
include "syl.mm"
include "negeqd.mm"

theorem cjneg
  let cA: class A


  assert |- ( A e. CC -> ( * ` -u A ) = -u ( * ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    cre
    cfv
    #
    ci
    @1
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
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
    cmin
    co
    #
    cneg
    #
    @1
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    cneg
    @0
    @6
    cneg
    #
    @8
    cneg
    #
    cmin
    co
    @8
    @6
    cmin
    co
    @5
    @10
    @0
    @6
    @8
    @0
    @6
    cA
    recl
    recnd
    #
    @0
    ci
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @8
    cc
    wcel
    ax-icn
    @0
    @7
    cA
    imcl
    recnd
    #
    ci
    @7
    mulcl
    sylancr
    #
    neg2subd
    @0
    @2
    @13
    @4
    @14
    cmin
    cA
    reneg
    @0
    @4
    ci
    @7
    cneg
    #
    cmul
    co
    #
    @14
    @0
    @3
    @20
    ci
    cmul
    cA
    imneg
    oveq2d
    @0
    @16
    @17
    @21
    @14
    wceq
    ax-icn
    @18
    ci
    @7
    mulneg2
    sylancr
    eqtrd
    oveq12d
    @0
    @6
    @8
    @15
    @19
    negsubdi2d
    3eqtr4d
    @0
    @1
    cc
    wcel
    @11
    @5
    wceq
    cA
    negcl
    @1
    remim
    syl
    @0
    @12
    @9
    cA
    remim
    negeqd
    3eqtr4d
end
