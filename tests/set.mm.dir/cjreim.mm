include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ccj.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "cjadd.mm"
include "syl2an.mm"
include "cjre.mm"
include "cjmul.mm"
include "cji.mm"
include "a1i.mm"
include "oveq12d.mm"
include "mulneg1.mm"
include "3eqtrd.mm"
include "oveqan12d.mm"
include "negsub.mm"

theorem cjreim
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( * ` ( A + ( _i x. B ) ) ) = ( A - ( _i x. B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    @2
    ccj
    cfv
    #
    caddc
    co
    #
    cA
    @2
    cneg
    #
    caddc
    co
    #
    cA
    @2
    cmin
    co
    #
    @0
    cA
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @3
    @6
    wceq
    @1
    cA
    recn
    #
    @1
    ci
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @11
    ax-icn
    cB
    recn
    #
    ci
    cB
    mulcl
    sylancr
    #
    cA
    @2
    cjadd
    syl2an
    @0
    @1
    @4
    cA
    @5
    @7
    caddc
    cA
    cjre
    @1
    @5
    ci
    ccj
    cfv
    #
    cB
    ccj
    cfv
    #
    cmul
    co
    #
    ci
    cneg
    #
    cB
    cmul
    co
    #
    @7
    @1
    @13
    @14
    @5
    @19
    wceq
    ax-icn
    @15
    ci
    cB
    cjmul
    sylancr
    @1
    @17
    @20
    @18
    cB
    cmul
    @17
    @20
    wceq
    @1
    cji
    a1i
    cB
    cjre
    oveq12d
    @1
    @13
    @14
    @21
    @7
    wceq
    ax-icn
    @15
    ci
    cB
    mulneg1
    sylancr
    3eqtrd
    oveqan12d
    @0
    @10
    @11
    @8
    @9
    wceq
    @1
    @12
    @16
    cA
    @2
    negsub
    syl2an
    3eqtrd
end
