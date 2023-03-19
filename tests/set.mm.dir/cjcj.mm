include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cjcl.mm"
include "recj.mm"
include "syl.mm"
include "eqtrd.mm"
include "cneg.mm"
include "imcj.mm"
include "negeqd.mm"
include "imcl.mm"
include "recnd.mm"
include "negnegd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "replim.mm"
include "3syl.mm"
include "3eqtr4d.mm"

theorem cjcj
  let cA: class A


  assert |- ( A e. CC -> ( * ` ( * ` A ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    ccj
    cfv
    #
    ccj
    cfv
    #
    cre
    cfv
    #
    ci
    @2
    cim
    cfv
    #
    cmul
    co
    #
    caddc
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
    caddc
    co
    @2
    cA
    @0
    @3
    @7
    @5
    @9
    caddc
    @0
    @3
    @1
    cre
    cfv
    #
    @7
    @0
    @1
    cc
    wcel
    #
    @3
    @10
    wceq
    cA
    cjcl
    #
    @1
    recj
    syl
    cA
    recj
    eqtrd
    @0
    @4
    @8
    ci
    cmul
    @0
    @4
    @1
    cim
    cfv
    #
    cneg
    #
    @8
    @0
    @11
    @4
    @14
    wceq
    @12
    @1
    imcj
    syl
    @0
    @14
    @8
    cneg
    #
    cneg
    @8
    @0
    @13
    @15
    cA
    imcj
    negeqd
    @0
    @8
    @0
    @8
    cA
    imcl
    recnd
    negnegd
    eqtrd
    eqtrd
    oveq2d
    oveq12d
    @0
    @11
    @2
    cc
    wcel
    @2
    @6
    wceq
    @12
    @1
    cjcl
    @2
    replim
    3syl
    cA
    replim
    3eqtr4d
end
