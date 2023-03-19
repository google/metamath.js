include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "chil.mm"
include "chos.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "hmopf.mm"
include "hoaddcl.mm"
include "syl2an.mm"
include "caddc.mm"
include "hmop.mm"
include "3expb.mm"
include "oveqan12d.mm"
include "anandirs.mm"
include "anim12i.mm"
include "cva.mm"
include "w3a.mm"
include "hosval.mm"
include "oveq2d.mm"
include "3expa.mm"
include "adantrl.mm"
include "simprl.mm"
include "ffvelrn.mm"
include "ad2ant2rl.mm"
include "ad2ant2l.mm"
include "his7.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "sylan.mm"
include "oveq1d.mm"
include "adantrr.mm"
include "ad2ant2r.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "ax-his2.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "elhmop.mm"
include "sylanbrc.mm"

theorem hmops
  let cT: class T
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( ( T e. HrmOp /\ U e. HrmOp ) -> ( T +op U ) e. HrmOp )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    wa
    #
    chil
    chil
    cT
    cU
    chos
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
    @4
    @1
    cT
    hmopf
    #
    cU
    hmopf
    #
    cT
    cU
    hoaddcl
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
    @5
    @6
    cT
    cfv
    #
    csp
    co
    #
    @5
    @6
    cU
    cfv
    #
    csp
    co
    #
    caddc
    co
    #
    @5
    cT
    cfv
    #
    @6
    csp
    co
    #
    @5
    cU
    cfv
    #
    @6
    csp
    co
    #
    caddc
    co
    #
    @8
    @10
    @0
    @1
    @18
    @23
    @28
    wceq
    @0
    @18
    wa
    @1
    @18
    wa
    @20
    @25
    @22
    @27
    caddc
    @0
    @16
    @17
    @20
    @25
    wceq
    @5
    @6
    cT
    hmop
    3expb
    @1
    @16
    @17
    @22
    @27
    wceq
    @5
    @6
    cU
    hmop
    3expb
    oveqan12d
    anandirs
    @2
    @12
    @13
    wa
    #
    @18
    @8
    @23
    wceq
    @0
    @12
    @1
    @13
    @14
    @15
    anim12i
    #
    @29
    @18
    wa
    #
    @8
    @5
    @19
    @21
    cva
    co
    #
    csp
    co
    #
    @23
    @29
    @17
    @8
    @33
    wceq
    #
    @16
    @12
    @13
    @17
    @34
    @12
    @13
    @17
    w3a
    @7
    @32
    @5
    csp
    @6
    cT
    cU
    hosval
    oveq2d
    3expa
    adantrl
    @31
    @16
    @19
    chil
    wcel
    #
    @21
    chil
    wcel
    #
    @33
    @23
    wceq
    @29
    @16
    @17
    simprl
    @12
    @17
    @35
    @13
    @16
    chil
    chil
    @6
    cT
    ffvelrn
    ad2ant2rl
    @13
    @17
    @36
    @12
    @16
    chil
    chil
    @6
    cU
    ffvelrn
    ad2ant2l
    @5
    @19
    @21
    his7
    syl3anc
    eqtrd
    sylan
    @2
    @29
    @18
    @10
    @28
    wceq
    @30
    @31
    @10
    @24
    @26
    cva
    co
    #
    @6
    csp
    co
    #
    @28
    @29
    @16
    @10
    @38
    wceq
    #
    @17
    @12
    @13
    @16
    @39
    @12
    @13
    @16
    w3a
    @9
    @37
    @6
    csp
    @5
    cT
    cU
    hosval
    oveq1d
    3expa
    adantrr
    @31
    @24
    chil
    wcel
    #
    @26
    chil
    wcel
    #
    @17
    @38
    @28
    wceq
    @12
    @16
    @40
    @13
    @17
    chil
    chil
    @5
    cT
    ffvelrn
    ad2ant2r
    @13
    @16
    @41
    @12
    @17
    chil
    chil
    @5
    cU
    ffvelrn
    ad2ant2lr
    @29
    @16
    @17
    simprr
    @24
    @26
    @6
    ax-his2
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
