include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "chil.mm"
include "chos.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "dmadjop.mm"
include "hoaddcl.mm"
include "syl2an.mm"
include "dmadjrn.mm"
include "syl.mm"
include "cva.mm"
include "caddc.mm"
include "adj2.mm"
include "3expb.mm"
include "adantlr.mm"
include "adantll.mm"
include "oveq12d.mm"
include "ffvelrnda.mm"
include "ad2ant2r.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "ax-his2.mm"
include "syl3anc.mm"
include "simprl.mm"
include "adjcl.mm"
include "ad2ant2rl.mm"
include "ad2ant2l.mm"
include "his7.mm"
include "3eqtr4rd.mm"
include "anim12i.mm"
include "hosval.mm"
include "3expa.mm"
include "sylan.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "ralrimivva.mm"
include "adjeq.mm"

theorem adjadd
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S e. dom adjh /\ T e. dom adjh ) -> ( adjh ` ( S +op T ) ) = ( ( adjh ` S ) +op ( adjh ` T ) ) )

  proof
    cS
    cado
    cdm
    #
    wcel
    #
    cT
    @0
    wcel
    #
    wa
    #
    chil
    chil
    cS
    cT
    chos
    co
    #
    wf
    #
    chil
    chil
    cS
    cado
    cfv
    #
    cT
    cado
    cfv
    #
    chos
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
    @1
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    @5
    @2
    cS
    dmadjop
    #
    cT
    dmadjop
    #
    cS
    cT
    hoaddcl
    syl2an
    @1
    chil
    chil
    @6
    wf
    #
    chil
    chil
    @7
    wf
    #
    @9
    @2
    @1
    @6
    @0
    wcel
    @21
    cS
    dmadjrn
    @6
    dmadjop
    syl
    #
    @2
    @7
    @0
    wcel
    @22
    cT
    dmadjrn
    @7
    dmadjop
    syl
    #
    @6
    @7
    hoaddcl
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
    @10
    @12
    @6
    cfv
    #
    @12
    @7
    cfv
    #
    cva
    co
    #
    csp
    co
    #
    @10
    cS
    cfv
    #
    @10
    cT
    cfv
    #
    cva
    co
    #
    @12
    csp
    co
    #
    @15
    @13
    @28
    @33
    @12
    csp
    co
    #
    @34
    @12
    csp
    co
    #
    caddc
    co
    #
    @10
    @29
    csp
    co
    #
    @10
    @30
    csp
    co
    #
    caddc
    co
    #
    @36
    @32
    @28
    @37
    @40
    @38
    @41
    caddc
    @1
    @27
    @37
    @40
    wceq
    #
    @2
    @1
    @25
    @26
    @43
    @10
    @12
    cS
    adj2
    3expb
    adantlr
    @2
    @27
    @38
    @41
    wceq
    #
    @1
    @2
    @25
    @26
    @44
    @10
    @12
    cT
    adj2
    3expb
    adantll
    oveq12d
    @28
    @33
    chil
    wcel
    #
    @34
    chil
    wcel
    #
    @26
    @36
    @39
    wceq
    @1
    @25
    @45
    @2
    @26
    @1
    chil
    chil
    @10
    cS
    @19
    ffvelrnda
    ad2ant2r
    @2
    @25
    @46
    @1
    @26
    @2
    chil
    chil
    @10
    cT
    @20
    ffvelrnda
    ad2ant2lr
    @3
    @25
    @26
    simprr
    @33
    @34
    @12
    ax-his2
    syl3anc
    @28
    @25
    @29
    chil
    wcel
    #
    @30
    chil
    wcel
    #
    @32
    @42
    wceq
    @3
    @25
    @26
    simprl
    @1
    @26
    @47
    @2
    @25
    @12
    cS
    adjcl
    ad2ant2rl
    @2
    @26
    @48
    @1
    @25
    @12
    cT
    adjcl
    ad2ant2l
    @10
    @29
    @30
    his7
    syl3anc
    3eqtr4rd
    @28
    @14
    @31
    @10
    csp
    @3
    @26
    @14
    @31
    wceq
    #
    @25
    @3
    @21
    @22
    wa
    @26
    @49
    @1
    @21
    @2
    @22
    @23
    @24
    anim12i
    @21
    @22
    @26
    @49
    @12
    @6
    @7
    hosval
    3expa
    sylan
    adantrl
    oveq2d
    @28
    @11
    @35
    @12
    csp
    @3
    @25
    @11
    @35
    wceq
    #
    @26
    @3
    @17
    @18
    wa
    @25
    @50
    @1
    @17
    @2
    @18
    @19
    @20
    anim12i
    @17
    @18
    @25
    @50
    @10
    cS
    cT
    hosval
    3expa
    sylan
    adantrr
    oveq1d
    3eqtr4rd
    ralrimivva
    vx
    vy
    @8
    @4
    adjeq
    syl3anc
end
