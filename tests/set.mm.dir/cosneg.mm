include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "ccos.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulneg12.mm"
include "mpan.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "mul2neg.mm"
include "oveq12d.mm"
include "negicn.mm"
include "mulcl.mm"
include "efcl.mm"
include "syl.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "negcl.mm"
include "cosval.mm"
include "3eqtr4d.mm"

theorem cosneg
  let cA: class A


  assert |- ( A e. CC -> ( cos ` -u A ) = ( cos ` A ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cneg
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @1
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
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    @4
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
    @1
    ccos
    cfv
    #
    cA
    ccos
    cfv
    @0
    @7
    @13
    c2
    cdiv
    @0
    @7
    @12
    @10
    caddc
    co
    @13
    @0
    @3
    @12
    @6
    @10
    caddc
    @0
    @2
    @11
    ce
    @0
    @11
    @2
    ci
    cc
    wcel
    #
    @0
    @11
    @2
    wceq
    ax-icn
    ci
    cA
    mulneg12
    mpan
    eqcomd
    fveq2d
    @0
    @5
    @9
    ce
    @15
    @0
    @5
    @9
    wceq
    ax-icn
    ci
    cA
    mul2neg
    mpan
    fveq2d
    oveq12d
    @0
    @12
    @10
    @0
    @11
    cc
    wcel
    #
    @12
    cc
    wcel
    @4
    cc
    wcel
    @0
    @16
    negicn
    @4
    cA
    mulcl
    mpan
    @11
    efcl
    syl
    @0
    @9
    cc
    wcel
    #
    @10
    cc
    wcel
    @15
    @0
    @17
    ax-icn
    ci
    cA
    mulcl
    mpan
    @9
    efcl
    syl
    addcomd
    eqtrd
    oveq1d
    @0
    @1
    cc
    wcel
    @14
    @8
    wceq
    cA
    negcl
    @1
    cosval
    syl
    cA
    cosval
    3eqtr4d
end
