include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "ce.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "cosval.mm"
include "syl.mm"
include "c1.mm"
include "ixi.mm"
include "oveq1i.mm"
include "mulass.mm"
include "mp3an12.mm"
include "mulm1.mm"
include "3eqtr3a.mm"
include "fveq2d.mm"
include "mulneg1i.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "3eqtri.mm"
include "negicn.mm"
include "mulid2.mm"
include "oveq12d.mm"
include "negcl.mm"
include "efcl.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "oveq1d.mm"

theorem coshval
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( _i x. A ) ) = ( ( ( exp ` A ) + ( exp ` -u A ) ) / 2 ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ccos
    cfv
    #
    ci
    @1
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
    cA
    ce
    cfv
    #
    cA
    cneg
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
    @0
    @1
    cc
    wcel
    #
    @2
    @9
    wceq
    ci
    cc
    wcel
    #
    @0
    @14
    ax-icn
    ci
    cA
    mulcl
    mpan
    @1
    cosval
    syl
    @0
    @8
    @13
    c2
    cdiv
    @0
    @8
    @12
    @10
    caddc
    co
    @13
    @0
    @4
    @12
    @7
    @10
    caddc
    @0
    @3
    @11
    ce
    @0
    ci
    ci
    cmul
    co
    #
    cA
    cmul
    co
    #
    c1
    cneg
    #
    cA
    cmul
    co
    @3
    @11
    @16
    @18
    cA
    cmul
    ixi
    oveq1i
    @15
    @15
    @0
    @17
    @3
    wceq
    ax-icn
    ax-icn
    ci
    ci
    cA
    mulass
    mp3an12
    cA
    mulm1
    3eqtr3a
    fveq2d
    @0
    @6
    cA
    ce
    @0
    @5
    ci
    cmul
    co
    #
    cA
    cmul
    co
    #
    c1
    cA
    cmul
    co
    @6
    cA
    @19
    c1
    cA
    cmul
    @19
    @16
    cneg
    @18
    cneg
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg1i
    @16
    @18
    ixi
    negeqi
    negneg1e1
    3eqtri
    oveq1i
    @5
    cc
    wcel
    @15
    @0
    @20
    @6
    wceq
    negicn
    ax-icn
    @5
    ci
    cA
    mulass
    mp3an12
    cA
    mulid2
    3eqtr3a
    fveq2d
    oveq12d
    @0
    @12
    @10
    @0
    @11
    cc
    wcel
    @12
    cc
    wcel
    cA
    negcl
    @11
    efcl
    syl
    cA
    efcl
    addcomd
    eqtrd
    oveq1d
    eqtrd
end
