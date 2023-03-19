include "cho.mm"
include "wcel.mm"
include "ccom.mm"
include "wceq.mm"
include "w3a.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wral.mm"
include "hmopf.mm"
include "fco.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wa.mm"
include "fvco3.mm"
include "sylan.mm"
include "oveq2d.mm"
include "ad2ant2l.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrnda.mm"
include "hmop.mm"
include "syl3anc.mm"
include "simplr.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "3adantl3.mm"
include "fveq1.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "ralrimivva.mm"
include "elhmop.mm"
include "sylanbrc.mm"

theorem hmopco
  let cT: class T
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( ( T e. HrmOp /\ U e. HrmOp /\ ( T o. U ) = ( U o. T ) ) -> ( T o. U ) e. HrmOp )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    cT
    cU
    ccom
    #
    cU
    cT
    ccom
    #
    wceq
    #
    w3a
    #
    chil
    chil
    @2
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @2
    cfv
    #
    csp
    co
    #
    @7
    @2
    cfv
    #
    @8
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
    @2
    cho
    wcel
    @0
    @1
    @6
    @4
    @0
    chil
    chil
    cT
    wf
    #
    chil
    chil
    cU
    wf
    #
    @6
    @1
    cT
    hmopf
    #
    cU
    hmopf
    #
    chil
    chil
    chil
    cT
    cU
    fco
    syl2an
    3adant3
    @5
    @13
    vx
    vy
    chil
    chil
    @5
    @7
    chil
    wcel
    #
    @8
    chil
    wcel
    #
    wa
    #
    wa
    @10
    @7
    @3
    cfv
    #
    @8
    csp
    co
    #
    @12
    @0
    @1
    @20
    @10
    @22
    wceq
    @4
    @0
    @1
    wa
    #
    @20
    wa
    #
    @10
    @7
    cT
    cfv
    #
    cU
    cfv
    #
    @8
    csp
    co
    #
    @22
    @24
    @10
    @7
    @8
    cU
    cfv
    #
    cT
    cfv
    #
    csp
    co
    #
    @25
    @28
    csp
    co
    #
    @27
    @1
    @19
    @10
    @30
    wceq
    @0
    @18
    @1
    @19
    wa
    @9
    @29
    @7
    csp
    @1
    @15
    @19
    @9
    @29
    wceq
    @17
    chil
    chil
    @8
    cT
    cU
    fvco3
    sylan
    oveq2d
    ad2ant2l
    @24
    @0
    @18
    @28
    chil
    wcel
    #
    @30
    @31
    wceq
    @0
    @1
    @20
    simpll
    @23
    @18
    @19
    simprl
    @1
    @19
    @32
    @0
    @18
    @1
    chil
    chil
    @8
    cU
    @17
    ffvelrnda
    ad2ant2l
    @7
    @28
    cT
    hmop
    syl3anc
    @24
    @1
    @25
    chil
    wcel
    #
    @19
    @31
    @27
    wceq
    @0
    @1
    @20
    simplr
    @0
    @18
    @33
    @1
    @19
    @0
    chil
    chil
    @7
    cT
    @16
    ffvelrnda
    ad2ant2r
    @23
    @18
    @19
    simprr
    @25
    @8
    cU
    hmop
    syl3anc
    3eqtrd
    @0
    @18
    @22
    @27
    wceq
    @1
    @19
    @0
    @18
    wa
    @21
    @26
    @8
    csp
    @0
    @14
    @18
    @21
    @26
    wceq
    @16
    chil
    chil
    @7
    cU
    cT
    fvco3
    sylan
    oveq1d
    ad2ant2r
    eqtr4d
    3adantl3
    @5
    @12
    @22
    wceq
    #
    @20
    @4
    @0
    @34
    @1
    @4
    @11
    @21
    @8
    csp
    @7
    @2
    @3
    fveq1
    oveq1d
    3ad2ant3
    adantr
    eqtr4d
    ralrimivva
    vx
    vy
    @2
    elhmop
    sylanbrc
end
