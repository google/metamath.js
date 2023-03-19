include "cc.mm"
include "wcel.mm"
include "cado.mm"
include "cdm.mm"
include "wa.mm"
include "chil.mm"
include "chot.mm"
include "co.mm"
include "wf.mm"
include "ccj.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "dmadjop.mm"
include "homulcl.mm"
include "sylan2.mm"
include "cjcl.mm"
include "dmadjrn.mm"
include "syl.mm"
include "syl2an.mm"
include "csm.mm"
include "cmul.mm"
include "adj2.mm"
include "3expb.mm"
include "adantll.mm"
include "oveq2d.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "ax-his3.mm"
include "syl3an2.mm"
include "3exp.mm"
include "expd.mm"
include "imp43.mm"
include "simpll.mm"
include "simprl.mm"
include "adjcl.mm"
include "ad2ant2l.mm"
include "his52.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"
include "homval.mm"
include "3expa.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "id.mm"
include "syl3an.mm"
include "adantrl.mm"
include "ralrimivva.mm"
include "adjeq.mm"

theorem adjmul
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ T e. dom adjh ) -> ( adjh ` ( A .op T ) ) = ( ( * ` A ) .op ( adjh ` T ) ) )

  proof
    cA
    cc
    wcel
    #
    cT
    cado
    cdm
    #
    wcel
    #
    wa
    #
    chil
    chil
    cA
    cT
    chot
    co
    #
    wf
    #
    chil
    chil
    cA
    ccj
    cfv
    #
    cT
    cado
    cfv
    #
    chot
    co
    #
    wf
    #
    vx
    cv
    #
    @4
    cfv
    #
    vy
    cv
    #
    csp
    co
    #
    @10
    @12
    @8
    cfv
    #
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @4
    cado
    cfv
    @8
    wceq
    @2
    @0
    chil
    chil
    cT
    wf
    #
    @5
    cT
    dmadjop
    #
    cA
    cT
    homulcl
    sylan2
    @0
    @6
    cc
    wcel
    #
    chil
    chil
    @7
    wf
    #
    @9
    @2
    cA
    cjcl
    #
    @2
    @7
    @1
    wcel
    @20
    cT
    dmadjrn
    @7
    dmadjop
    syl
    #
    @6
    @7
    homulcl
    syl2an
    @3
    @16
    vx
    vy
    chil
    chil
    @3
    @10
    chil
    wcel
    #
    @12
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    @10
    cT
    cfv
    #
    csm
    co
    #
    @12
    csp
    co
    #
    @10
    @6
    @12
    @7
    cfv
    #
    csm
    co
    #
    csp
    co
    #
    @13
    @15
    @26
    cA
    @27
    @12
    csp
    co
    #
    cmul
    co
    #
    cA
    @10
    @30
    csp
    co
    #
    cmul
    co
    #
    @29
    @32
    @26
    @33
    @35
    cA
    cmul
    @2
    @25
    @33
    @35
    wceq
    #
    @0
    @2
    @23
    @24
    @37
    @10
    @12
    cT
    adj2
    3expb
    adantll
    oveq2d
    @0
    @2
    @23
    @24
    @29
    @34
    wceq
    #
    @0
    @2
    @23
    @24
    @38
    wi
    @0
    @2
    @23
    wa
    #
    @24
    @38
    @39
    @0
    @27
    chil
    wcel
    @24
    @38
    @2
    chil
    chil
    @10
    cT
    @18
    ffvelrnda
    cA
    @27
    @12
    ax-his3
    syl3an2
    3exp
    expd
    imp43
    @26
    @0
    @23
    @30
    chil
    wcel
    #
    @32
    @36
    wceq
    @0
    @2
    @25
    simpll
    @3
    @23
    @24
    simprl
    @2
    @24
    @40
    @0
    @23
    @12
    cT
    adjcl
    ad2ant2l
    cA
    @10
    @30
    his52
    syl3anc
    3eqtr4d
    @26
    @11
    @28
    @12
    csp
    @3
    @23
    @11
    @28
    wceq
    #
    @24
    @0
    @2
    @23
    @41
    @2
    @0
    @17
    @23
    @41
    @18
    cA
    @10
    cT
    homval
    syl3an2
    3expa
    adantrr
    oveq1d
    @26
    @14
    @31
    @10
    csp
    @3
    @24
    @14
    @31
    wceq
    #
    @23
    @0
    @2
    @24
    @42
    @0
    @19
    @2
    @20
    @24
    @24
    @42
    @21
    @22
    @24
    id
    @6
    @12
    @7
    homval
    syl3an
    3expa
    adantrl
    oveq2d
    3eqtr4d
    ralrimivva
    vx
    vy
    @8
    @4
    adjeq
    syl3anc
end
