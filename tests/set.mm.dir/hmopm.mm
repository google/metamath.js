include "cr.mm"
include "wcel.mm"
include "cho.mm"
include "wa.mm"
include "chil.mm"
include "chot.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "recn.mm"
include "hmopf.mm"
include "homulcl.mm"
include "syl2an.mm"
include "ccj.mm"
include "cmul.mm"
include "cjre.mm"
include "hmop.mm"
include "3expb.mm"
include "oveqan12d.mm"
include "anassrs.mm"
include "anim12i.mm"
include "csm.mm"
include "homval.mm"
include "3expa.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrn.mm"
include "ad2ant2l.mm"
include "his5.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "sylan.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "ax-his3.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "elhmop.mm"
include "sylanbrc.mm"

theorem hmopm
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let cU: class U


  assert |- ( ( A e. RR /\ T e. HrmOp ) -> ( A .op T ) e. HrmOp )

  proof
    cA
    cr
    wcel
    #
    cT
    cho
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
    vx
    cv
    #
    vy
    cv
    #
    @3
    cfv
    #
    csp
    co
    #
    @5
    @3
    cfv
    #
    @6
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
    @3
    cho
    wcel
    @0
    cA
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    @4
    @1
    cA
    recn
    #
    cT
    hmopf
    #
    cA
    cT
    homulcl
    syl2an
    @2
    @11
    vx
    vy
    chil
    chil
    @2
    @5
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    wa
    #
    wa
    cA
    ccj
    cfv
    #
    @5
    @6
    cT
    cfv
    #
    csp
    co
    #
    cmul
    co
    #
    cA
    @5
    cT
    cfv
    #
    @6
    csp
    co
    #
    cmul
    co
    #
    @8
    @10
    @0
    @1
    @18
    @22
    @25
    wceq
    @0
    @1
    @18
    wa
    @19
    cA
    @21
    @24
    cmul
    cA
    cjre
    @1
    @16
    @17
    @21
    @24
    wceq
    @5
    @6
    cT
    hmop
    3expb
    oveqan12d
    anassrs
    @2
    @12
    @13
    wa
    #
    @18
    @8
    @22
    wceq
    @0
    @12
    @1
    @13
    @14
    @15
    anim12i
    #
    @26
    @18
    wa
    #
    @8
    @5
    cA
    @20
    csm
    co
    #
    csp
    co
    #
    @22
    @28
    @7
    @29
    @5
    csp
    @26
    @17
    @7
    @29
    wceq
    #
    @16
    @12
    @13
    @17
    @31
    cA
    @6
    cT
    homval
    3expa
    adantrl
    oveq2d
    @28
    @12
    @16
    @20
    chil
    wcel
    #
    @30
    @22
    wceq
    @12
    @13
    @18
    simpll
    #
    @26
    @16
    @17
    simprl
    @13
    @17
    @32
    @12
    @16
    chil
    chil
    @6
    cT
    ffvelrn
    ad2ant2l
    cA
    @5
    @20
    his5
    syl3anc
    eqtrd
    sylan
    @2
    @26
    @18
    @10
    @25
    wceq
    @27
    @28
    @10
    cA
    @23
    csm
    co
    #
    @6
    csp
    co
    #
    @25
    @28
    @9
    @34
    @6
    csp
    @26
    @16
    @9
    @34
    wceq
    #
    @17
    @12
    @13
    @16
    @36
    cA
    @5
    cT
    homval
    3expa
    adantrr
    oveq1d
    @28
    @12
    @23
    chil
    wcel
    #
    @17
    @35
    @25
    wceq
    @33
    @13
    @16
    @37
    @12
    @17
    chil
    chil
    @5
    cT
    ffvelrn
    ad2ant2lr
    @26
    @16
    @17
    simprr
    cA
    @23
    @6
    ax-his3
    syl3anc
    eqtrd
    sylan
    3eqtr4d
    ralrimivva
    vx
    vy
    @3
    elhmop
    sylanbrc
end
