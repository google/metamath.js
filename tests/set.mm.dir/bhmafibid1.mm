include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cre.mm"
include "cim.mm"
include "simpll.mm"
include "recnd.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simplr.mm"
include "mulcld.mm"
include "addcld.mm"
include "simprl.mm"
include "simprr.mm"
include "replimd.mm"
include "remuld.mm"
include "crred.mm"
include "oveq12d.mm"
include "crimd.mm"
include "eqtrd.mm"
include "immuld.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "absmuld.mm"
include "abscld.mm"
include "sqmuld.mm"
include "absreimsq.mm"
include "oveqan12d.mm"
include "3eqtrd.mm"
include "wceq.mm"
include "remulcld.mm"
include "resubcld.mm"
include "readdcld.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem bhmafibid1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( ( A ^ 2 ) + ( B ^ 2 ) ) x. ( ( C ^ 2 ) + ( D ^ 2 ) ) ) = ( ( ( ( A x. C ) - ( B x. D ) ) ^ 2 ) + ( ( ( A x. D ) + ( B x. C ) ) ^ 2 ) ) )

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
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cC
    ci
    cD
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cC
    cmul
    co
    #
    cB
    cD
    cmul
    co
    #
    cmin
    co
    #
    ci
    cA
    cD
    cmul
    co
    #
    cB
    cC
    cmul
    co
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
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    caddc
    co
    #
    cC
    c2
    cexp
    co
    cD
    c2
    cexp
    co
    caddc
    co
    #
    cmul
    co
    #
    @16
    c2
    cexp
    co
    @19
    c2
    cexp
    co
    caddc
    co
    #
    @6
    @12
    @22
    c2
    cexp
    @6
    @11
    @21
    cabs
    @6
    @11
    @11
    cre
    cfv
    #
    ci
    @11
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @21
    @6
    @11
    @6
    @8
    @10
    @6
    cA
    @7
    @6
    cA
    @0
    @1
    @5
    simpll
    #
    recnd
    @6
    ci
    cB
    ci
    cc
    wcel
    @6
    ax-icn
    a1i
    #
    @6
    cB
    @0
    @1
    @5
    simplr
    #
    recnd
    mulcld
    addcld
    #
    @6
    cC
    @9
    @6
    cC
    @2
    @3
    @4
    simprl
    #
    recnd
    @6
    ci
    cD
    @32
    @6
    cD
    @2
    @3
    @4
    simprr
    #
    recnd
    mulcld
    addcld
    #
    mulcld
    replimd
    @6
    @28
    @16
    @30
    @20
    caddc
    @6
    @28
    @8
    cre
    cfv
    #
    @10
    cre
    cfv
    #
    cmul
    co
    #
    @8
    cim
    cfv
    #
    @10
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    @16
    @6
    @8
    @10
    @34
    @37
    remuld
    @6
    @40
    @14
    @43
    @15
    cmin
    @6
    @38
    cA
    @39
    cC
    cmul
    @6
    cA
    cB
    @31
    @33
    crred
    #
    @6
    cC
    cD
    @35
    @36
    crred
    #
    oveq12d
    @6
    @41
    cB
    @42
    cD
    cmul
    @6
    cA
    cB
    @31
    @33
    crimd
    #
    @6
    cC
    cD
    @35
    @36
    crimd
    #
    oveq12d
    oveq12d
    eqtrd
    @6
    @29
    @19
    ci
    cmul
    @6
    @29
    @38
    @42
    cmul
    co
    #
    @41
    @39
    cmul
    co
    #
    caddc
    co
    @19
    @6
    @8
    @10
    @34
    @37
    immuld
    @6
    @48
    @17
    @49
    @18
    caddc
    @6
    @38
    cA
    @42
    cD
    cmul
    @44
    @47
    oveq12d
    @6
    @41
    cB
    @39
    cC
    cmul
    @46
    @45
    oveq12d
    oveq12d
    eqtrd
    oveq2d
    oveq12d
    eqtrd
    fveq2d
    oveq1d
    @6
    @13
    @8
    cabs
    cfv
    #
    @10
    cabs
    cfv
    #
    cmul
    co
    #
    c2
    cexp
    co
    @50
    c2
    cexp
    co
    #
    @51
    c2
    cexp
    co
    #
    cmul
    co
    @26
    @6
    @12
    @52
    c2
    cexp
    @6
    @8
    @10
    @34
    @37
    absmuld
    oveq1d
    @6
    @50
    @51
    @6
    @50
    @6
    @8
    @34
    abscld
    recnd
    @6
    @51
    @6
    @10
    @37
    abscld
    recnd
    sqmuld
    @2
    @5
    @53
    @24
    @54
    @25
    cmul
    cA
    cB
    absreimsq
    cC
    cD
    absreimsq
    oveqan12d
    3eqtrd
    @6
    @16
    cr
    wcel
    @19
    cr
    wcel
    @23
    @27
    wceq
    @6
    @14
    @15
    @6
    cA
    cC
    @31
    @35
    remulcld
    @6
    cB
    cD
    @33
    @36
    remulcld
    resubcld
    @6
    @17
    @18
    @6
    cA
    cD
    @31
    @36
    remulcld
    @6
    cB
    cC
    @33
    @35
    remulcld
    readdcld
    @16
    @19
    absreimsq
    syl2anc
    3eqtr3d
end
