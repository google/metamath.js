include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cim.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "negdid.mm"
include "replim.mm"
include "negeqd.mm"
include "wceq.mm"
include "mulneg2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "cr.mm"
include "renegcld.mm"
include "crim.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem imneg
  let cA: class A


  assert |- ( A e. CC -> ( Im ` -u A ) = -u ( Im ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    cim
    cfv
    cA
    cre
    cfv
    #
    cneg
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
    cim
    cfv
    #
    @5
    @0
    @1
    @7
    cim
    @0
    @2
    ci
    @4
    cmul
    co
    #
    caddc
    co
    #
    cneg
    @3
    @9
    cneg
    #
    caddc
    co
    @1
    @7
    @0
    @2
    @9
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
    @4
    cc
    wcel
    #
    @9
    cc
    wcel
    ax-icn
    @0
    @4
    cA
    imcl
    #
    recnd
    #
    ci
    @4
    mulcl
    sylancr
    negdid
    @0
    cA
    @10
    cA
    replim
    negeqd
    @0
    @6
    @11
    @3
    caddc
    @0
    @13
    @14
    @6
    @11
    wceq
    ax-icn
    @16
    ci
    @4
    mulneg2
    sylancr
    oveq2d
    3eqtr4d
    fveq2d
    @0
    @3
    cr
    wcel
    @5
    cr
    wcel
    @8
    @5
    wceq
    @0
    @2
    @12
    renegcld
    @0
    @4
    @15
    renegcld
    @3
    @5
    crim
    syl2anc
    eqtrd
end
