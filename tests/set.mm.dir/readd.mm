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
include "cr.mm"
include "recl.mm"
include "adantr.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "adantl.mm"
include "add4d.mm"
include "replim.mm"
include "oveqan12d.mm"
include "a1i.mm"
include "adddid.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "readdcl.mm"
include "syl2an.mm"
include "crre.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem readd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( Re ` ( A + B ) ) = ( ( Re ` A ) + ( Re ` B ) ) )

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
    cA
    cre
    cfv
    #
    cB
    cre
    cfv
    #
    caddc
    co
    #
    ci
    cA
    cim
    cfv
    #
    cB
    cim
    cfv
    #
    caddc
    co
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
    @6
    @2
    @3
    @11
    cre
    @2
    @4
    ci
    @7
    cmul
    co
    #
    caddc
    co
    #
    @5
    ci
    @8
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @6
    @13
    @15
    caddc
    co
    #
    caddc
    co
    @3
    @11
    @2
    @4
    @13
    @5
    @15
    @2
    @4
    @0
    @4
    cr
    wcel
    #
    @1
    cA
    recl
    #
    adantr
    recnd
    @2
    ci
    cc
    wcel
    #
    @7
    cc
    wcel
    @13
    cc
    wcel
    ax-icn
    @2
    @7
    @0
    @7
    cr
    wcel
    #
    @1
    cA
    imcl
    #
    adantr
    recnd
    #
    ci
    @7
    mulcl
    sylancr
    @2
    @5
    @1
    @5
    cr
    wcel
    #
    @0
    cB
    recl
    #
    adantl
    recnd
    @2
    @20
    @8
    cc
    wcel
    @15
    cc
    wcel
    ax-icn
    @2
    @8
    @1
    @8
    cr
    wcel
    #
    @0
    cB
    imcl
    #
    adantl
    recnd
    #
    ci
    @8
    mulcl
    sylancr
    add4d
    @0
    @1
    cA
    @14
    cB
    @16
    caddc
    cA
    replim
    cB
    replim
    oveqan12d
    @2
    @10
    @17
    @6
    caddc
    @2
    ci
    @7
    @8
    @20
    @2
    ax-icn
    a1i
    @23
    @28
    adddid
    oveq2d
    3eqtr4d
    fveq2d
    @2
    @6
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @12
    @6
    wceq
    @0
    @18
    @24
    @29
    @1
    @19
    @25
    @4
    @5
    readdcl
    syl2an
    @0
    @21
    @26
    @30
    @1
    @22
    @27
    @7
    @8
    readdcl
    syl2an
    @6
    @9
    crre
    syl2anc
    eqtrd
end
