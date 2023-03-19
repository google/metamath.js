include "cc.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ccos.mm"
include "csin.mm"
include "replim.mm"
include "fveq2d.mm"
include "wceq.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efadd.mm"
include "syl2anc.mm"
include "efival.mm"
include "syl.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem efeul
  let cA: class A


  assert |- ( A e. CC -> ( exp ` A ) = ( ( exp ` ( Re ` A ) ) x. ( ( cos ` ( Im ` A ) ) + ( _i x. ( sin ` ( Im ` A ) ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ce
    cfv
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
    #
    ce
    cfv
    #
    @1
    ce
    cfv
    #
    @3
    ce
    cfv
    #
    cmul
    co
    #
    @6
    @2
    ccos
    cfv
    ci
    @2
    csin
    cfv
    cmul
    co
    caddc
    co
    #
    cmul
    co
    @0
    cA
    @4
    ce
    cA
    replim
    fveq2d
    @0
    @1
    cc
    wcel
    @3
    cc
    wcel
    #
    @5
    @8
    wceq
    @0
    @1
    cA
    recl
    recnd
    @0
    ci
    cc
    wcel
    @2
    cc
    wcel
    #
    @10
    ax-icn
    @0
    @2
    cA
    imcl
    recnd
    #
    ci
    @2
    mulcl
    sylancr
    @1
    @3
    efadd
    syl2anc
    @0
    @7
    @9
    @6
    cmul
    @0
    @11
    @7
    @9
    wceq
    @12
    @2
    efival
    syl
    oveq2d
    3eqtrd
end
