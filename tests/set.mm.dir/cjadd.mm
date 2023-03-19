include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "cmin.mm"
include "ccj.mm"
include "readd.mm"
include "imadd.mm"
include "oveq2d.mm"
include "ax-icn.mm"
include "a1i.mm"
include "cr.mm"
include "imcl.mm"
include "adantr.mm"
include "recnd.mm"
include "adantl.mm"
include "adddid.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "recl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addsub4d.mm"
include "wceq.mm"
include "addcl.mm"
include "remim.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"

theorem cjadd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( * ` ( A + B ) ) = ( ( * ` A ) + ( * ` B ) ) )

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
    cA
    cB
    caddc
    co
    #
    cre
    cfv
    #
    ci
    @3
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
    cmin
    co
    #
    caddc
    co
    #
    @3
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    cB
    ccj
    cfv
    #
    caddc
    co
    @2
    @7
    @8
    @12
    caddc
    co
    #
    @10
    @14
    caddc
    co
    #
    cmin
    co
    @16
    @2
    @4
    @20
    @6
    @21
    cmin
    cA
    cB
    readd
    @2
    @6
    ci
    @9
    @13
    caddc
    co
    #
    cmul
    co
    @21
    @2
    @5
    @22
    ci
    cmul
    cA
    cB
    imadd
    oveq2d
    @2
    ci
    @9
    @13
    ci
    cc
    wcel
    #
    @2
    ax-icn
    a1i
    @2
    @9
    @0
    @9
    cr
    wcel
    @1
    cA
    imcl
    adantr
    recnd
    #
    @2
    @13
    @1
    @13
    cr
    wcel
    @0
    cB
    imcl
    adantl
    recnd
    #
    adddid
    eqtrd
    oveq12d
    @2
    @8
    @12
    @10
    @14
    @2
    @8
    @0
    @8
    cr
    wcel
    @1
    cA
    recl
    adantr
    recnd
    @2
    @12
    @1
    @12
    cr
    wcel
    @0
    cB
    recl
    adantl
    recnd
    @2
    @23
    @9
    cc
    wcel
    @10
    cc
    wcel
    ax-icn
    @24
    ci
    @9
    mulcl
    sylancr
    @2
    @23
    @13
    cc
    wcel
    @14
    cc
    wcel
    ax-icn
    @25
    ci
    @13
    mulcl
    sylancr
    addsub4d
    eqtrd
    @2
    @3
    cc
    wcel
    @17
    @7
    wceq
    cA
    cB
    addcl
    @3
    remim
    syl
    @0
    @1
    @18
    @11
    @19
    @15
    caddc
    cA
    remim
    cB
    remim
    oveqan12d
    3eqtr4d
end
