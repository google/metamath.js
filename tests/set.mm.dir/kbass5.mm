include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "ck.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "csp.mm"
include "csm.mm"
include "kbval.mm"
include "3expa.mm"
include "adantll.mm"
include "fveq2d.mm"
include "simplll.mm"
include "simpllr.mm"
include "cc.mm"
include "simpr.mm"
include "simplrr.mm"
include "hicl.mm"
include "syl2anc.mm"
include "simplrl.mm"
include "hvmulcl.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "wf.mm"
include "kbop.mm"
include "adantl.mm"
include "fvco3.mm"
include "sylan.mm"
include "oveq2d.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "adantr.mm"
include "cmul.mm"
include "ax-his3.mm"
include "oveq1d.mm"
include "ax-hvmulass.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "fco.mm"
include "syl2an.mm"
include "anasss.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "mpbird.mm"

theorem kbass5
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( A ketbra B ) o. ( C ketbra D ) ) = ( ( ( A ketbra B ) ` C ) ketbra D ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    ck
    co
    #
    cC
    cD
    ck
    co
    #
    ccom
    #
    cC
    @7
    cfv
    #
    cD
    ck
    co
    #
    wceq
    #
    vx
    cv
    #
    @9
    cfv
    #
    @13
    @11
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @6
    @16
    vx
    chil
    @6
    @13
    chil
    wcel
    #
    wa
    #
    @13
    @8
    cfv
    #
    @7
    cfv
    #
    @13
    cD
    csp
    co
    #
    cC
    csm
    co
    #
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    @14
    @15
    @19
    @21
    @23
    @7
    cfv
    #
    @25
    @19
    @20
    @23
    @7
    @5
    @18
    @20
    @23
    wceq
    #
    @2
    @3
    @4
    @18
    @27
    cC
    cD
    @13
    kbval
    3expa
    adantll
    fveq2d
    @19
    @0
    @1
    @23
    chil
    wcel
    #
    @26
    @25
    wceq
    @0
    @1
    @5
    @18
    simplll
    #
    @0
    @1
    @5
    @18
    simpllr
    #
    @19
    @22
    cc
    wcel
    #
    @3
    @28
    @19
    @18
    @4
    @31
    @6
    @18
    simpr
    #
    @2
    @3
    @4
    @18
    simplrr
    #
    @13
    cD
    hicl
    syl2anc
    #
    @2
    @3
    @4
    @18
    simplrl
    #
    @22
    cC
    hvmulcl
    syl2anc
    cA
    cB
    @23
    kbval
    syl3anc
    eqtrd
    @6
    chil
    chil
    @8
    wf
    #
    @18
    @14
    @21
    wceq
    @5
    @36
    @2
    cC
    cD
    kbop
    #
    adantl
    chil
    chil
    @13
    @7
    @8
    fvco3
    sylan
    @19
    @22
    @10
    csm
    co
    #
    @22
    cC
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    csm
    co
    #
    @15
    @25
    @19
    @10
    @40
    @22
    csm
    @19
    @0
    @1
    @3
    @10
    @40
    wceq
    @29
    @30
    @35
    cA
    cB
    cC
    kbval
    syl3anc
    oveq2d
    @19
    @10
    chil
    wcel
    #
    @4
    @18
    @15
    @38
    wceq
    @6
    @42
    @18
    @2
    @3
    @42
    @4
    @2
    chil
    chil
    cC
    @7
    cA
    cB
    kbop
    #
    ffvelrnda
    #
    adantrr
    adantr
    @33
    @32
    @10
    cD
    @13
    kbval
    syl3anc
    @19
    @25
    @22
    @39
    cmul
    co
    #
    cA
    csm
    co
    #
    @41
    @19
    @24
    @45
    cA
    csm
    @19
    @31
    @3
    @1
    @24
    @45
    wceq
    @34
    @35
    @30
    @22
    cC
    cB
    ax-his3
    syl3anc
    oveq1d
    @19
    @31
    @39
    cc
    wcel
    #
    @0
    @46
    @41
    wceq
    @34
    @19
    @3
    @1
    @47
    @35
    @30
    cC
    cB
    hicl
    syl2anc
    @29
    @22
    @39
    cA
    ax-hvmulass
    syl3anc
    eqtrd
    3eqtr4d
    3eqtr4d
    ralrimiva
    @6
    chil
    chil
    @9
    wf
    #
    chil
    chil
    @11
    wf
    #
    @12
    @17
    wb
    #
    @2
    chil
    chil
    @7
    wf
    @36
    @48
    @5
    @43
    @37
    chil
    chil
    chil
    @7
    @8
    fco
    syl2an
    @2
    @3
    @4
    @49
    @2
    @3
    wa
    @42
    @4
    @49
    @44
    @10
    cD
    kbop
    sylan
    anasss
    @48
    @9
    chil
    wfn
    @11
    chil
    wfn
    @50
    @49
    chil
    chil
    @9
    ffn
    chil
    chil
    @11
    ffn
    vx
    chil
    @9
    @11
    eqfnfv
    syl2an
    syl2anc
    mpbird
end
