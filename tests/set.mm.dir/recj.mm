include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cim.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "negsubd.mm"
include "wceq.mm"
include "mulneg2.mm"
include "oveq2d.mm"
include "remim.mm"
include "3eqtr4rd.mm"
include "fveq2d.mm"
include "cr.mm"
include "renegcld.mm"
include "crre.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem recj
  let cA: class A


  assert |- ( A e. CC -> ( Re ` ( * ` A ) ) = ( Re ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccj
    cfv
    #
    cre
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
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    #
    @2
    @0
    @1
    @6
    cre
    @0
    @2
    ci
    @3
    cmul
    co
    #
    cneg
    #
    caddc
    co
    @2
    @8
    cmin
    co
    @6
    @1
    @0
    @2
    @8
    @0
    @2
    cA
    recl
    #
    recnd
    @0
    ci
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @8
    cc
    wcel
    ax-icn
    @0
    @3
    cA
    imcl
    #
    recnd
    #
    ci
    @3
    mulcl
    sylancr
    negsubd
    @0
    @5
    @9
    @2
    caddc
    @0
    @11
    @12
    @5
    @9
    wceq
    ax-icn
    @14
    ci
    @3
    mulneg2
    sylancr
    oveq2d
    cA
    remim
    3eqtr4rd
    fveq2d
    @0
    @2
    cr
    wcel
    @4
    cr
    wcel
    @7
    @2
    wceq
    @10
    @0
    @3
    @13
    renegcld
    @2
    @4
    crre
    syl2anc
    eqtrd
end
