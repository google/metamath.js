include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "ccos.mm"
include "csin.mm"
include "cmin.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulneg12.mm"
include "mpan.mm"
include "fveq2d.mm"
include "caddc.mm"
include "negcl.mm"
include "efival.mm"
include "syl.mm"
include "cosneg.mm"
include "sinneg.mm"
include "oveq2d.mm"
include "sincl.mm"
include "mulneg2.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "coscl.mm"
include "mulcl.mm"
include "negsubd.mm"

theorem efmival
  let cA: class A


  assert |- ( A e. CC -> ( exp ` ( -u _i x. A ) ) = ( ( cos ` A ) - ( _i x. ( sin ` A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cneg
    cA
    cmul
    co
    #
    ce
    cfv
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
    cA
    ccos
    cfv
    #
    ci
    cA
    csin
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @0
    @1
    @3
    ce
    ci
    cc
    wcel
    #
    @0
    @1
    @3
    wceq
    ax-icn
    ci
    cA
    mulneg12
    mpan
    fveq2d
    @0
    @4
    @2
    ccos
    cfv
    #
    ci
    @2
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    @0
    @2
    cc
    wcel
    @4
    @13
    wceq
    cA
    negcl
    @2
    efival
    syl
    @0
    @13
    @5
    @7
    cneg
    #
    caddc
    co
    @8
    @0
    @10
    @5
    @12
    @14
    caddc
    cA
    cosneg
    @0
    @12
    ci
    @6
    cneg
    #
    cmul
    co
    #
    @14
    @0
    @11
    @15
    ci
    cmul
    cA
    sinneg
    oveq2d
    @0
    @9
    @6
    cc
    wcel
    #
    @16
    @14
    wceq
    ax-icn
    cA
    sincl
    #
    ci
    @6
    mulneg2
    sylancr
    eqtrd
    oveq12d
    @0
    @5
    @7
    cA
    coscl
    @0
    @9
    @17
    @7
    cc
    wcel
    ax-icn
    @18
    ci
    @6
    mulcl
    sylancr
    negsubd
    eqtrd
    eqtrd
    eqtrd
end
