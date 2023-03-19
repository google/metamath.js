include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "chil.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "clo.mm"
include "dmadjrn.mm"
include "dmadjop.mm"
include "syl.mm"
include "wa.mm"
include "csp.mm"
include "w3a.mm"
include "caddc.mm"
include "simp2.mm"
include "adjcl.mm"
include "hvmulcl.mm"
include "sylan2.mm"
include "an12s.mm"
include "adantrr.mm"
include "3adant2.mm"
include "adantrl.mm"
include "his7.mm"
include "syl3anc.mm"
include "ccj.mm"
include "cmul.mm"
include "adj2.mm"
include "3adant3l.mm"
include "oveq2d.mm"
include "simp3l.mm"
include "ffvelrnda.mm"
include "3adant3.mm"
include "simp3r.mm"
include "his5.mm"
include "3eqtr4d.mm"
include "3adant3r.mm"
include "oveq12d.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "syl3an3.mm"
include "eqtr3d.mm"
include "3eqtr2rd.mm"
include "3com23.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "wb.mm"
include "syl2an.mm"
include "anandis.mm"
include "hial2eq2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "exp32.mm"
include "ralrimdv.mm"
include "ralrimivv.mm"
include "ellnop.mm"
include "sylanbrc.mm"

theorem adjlnop
  let cT: class T
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. dom adjh -> ( adjh ` T ) e. LinOp )

  proof
    cT
    cado
    cdm
    #
    wcel
    #
    chil
    chil
    cT
    cado
    cfv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    @2
    cfv
    #
    @4
    @5
    @2
    cfv
    #
    csm
    co
    #
    @7
    @2
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vy
    chil
    wral
    vx
    cc
    wral
    @2
    clo
    wcel
    @1
    @2
    @0
    wcel
    @3
    cT
    dmadjrn
    @2
    dmadjop
    syl
    @1
    @15
    vx
    vy
    cc
    chil
    @1
    @4
    cc
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    #
    @14
    vz
    chil
    @1
    @18
    @7
    chil
    wcel
    #
    @14
    @1
    @18
    @19
    wa
    #
    wa
    #
    vw
    cv
    #
    @9
    csp
    co
    #
    @22
    @13
    csp
    co
    #
    wceq
    #
    vw
    chil
    wral
    #
    @14
    @21
    @25
    vw
    chil
    @1
    @20
    @22
    chil
    wcel
    #
    @25
    @1
    @27
    @20
    @25
    @1
    @27
    @20
    w3a
    #
    @24
    @22
    @11
    csp
    co
    #
    @22
    @12
    csp
    co
    #
    caddc
    co
    #
    @22
    cT
    cfv
    #
    @6
    csp
    co
    #
    @32
    @7
    csp
    co
    #
    caddc
    co
    #
    @23
    @28
    @27
    @11
    chil
    wcel
    #
    @12
    chil
    wcel
    #
    @24
    @31
    wceq
    @1
    @27
    @20
    simp2
    @1
    @20
    @36
    @27
    @1
    @18
    @36
    @19
    @16
    @1
    @17
    @36
    @1
    @17
    wa
    @16
    @10
    chil
    wcel
    #
    @36
    @5
    cT
    adjcl
    #
    @4
    @10
    hvmulcl
    sylan2
    an12s
    #
    adantrr
    3adant2
    @1
    @20
    @37
    @27
    @1
    @19
    @37
    @18
    @7
    cT
    adjcl
    #
    adantrl
    3adant2
    @22
    @11
    @12
    his7
    syl3anc
    @28
    @33
    @29
    @34
    @30
    caddc
    @1
    @27
    @18
    @33
    @29
    wceq
    @19
    @1
    @27
    @18
    w3a
    #
    @4
    ccj
    cfv
    #
    @32
    @5
    csp
    co
    #
    cmul
    co
    #
    @43
    @22
    @10
    csp
    co
    #
    cmul
    co
    #
    @33
    @29
    @42
    @44
    @46
    @43
    cmul
    @1
    @27
    @17
    @44
    @46
    wceq
    @16
    @22
    @5
    cT
    adj2
    3adant3l
    oveq2d
    @42
    @16
    @32
    chil
    wcel
    #
    @17
    @33
    @45
    wceq
    @1
    @27
    @16
    @17
    simp3l
    #
    @1
    @27
    @48
    @18
    @1
    chil
    chil
    @22
    cT
    cT
    dmadjop
    ffvelrnda
    #
    3adant3
    @1
    @27
    @16
    @17
    simp3r
    @4
    @32
    @5
    his5
    syl3anc
    @42
    @16
    @27
    @38
    @29
    @47
    wceq
    @49
    @1
    @27
    @18
    simp2
    @1
    @18
    @38
    @27
    @1
    @17
    @38
    @16
    @39
    adantrl
    3adant2
    @4
    @22
    @10
    his5
    syl3anc
    3eqtr4d
    3adant3r
    @1
    @27
    @19
    @34
    @30
    wceq
    @18
    @22
    @7
    cT
    adj2
    3adant3l
    oveq12d
    @28
    @32
    @8
    csp
    co
    #
    @35
    @23
    @28
    @48
    @6
    chil
    wcel
    #
    @19
    @51
    @35
    wceq
    @1
    @27
    @48
    @20
    @50
    3adant3
    @20
    @1
    @52
    @27
    @18
    @52
    @19
    @4
    @5
    hvmulcl
    #
    adantr
    3ad2ant3
    @1
    @27
    @18
    @19
    simp3r
    @32
    @6
    @7
    his7
    syl3anc
    @20
    @1
    @27
    @8
    chil
    wcel
    #
    @51
    @23
    wceq
    @18
    @52
    @19
    @54
    @53
    @6
    @7
    hvaddcl
    sylan
    #
    @22
    @8
    cT
    adj2
    syl3an3
    eqtr3d
    3eqtr2rd
    3com23
    3expa
    ralrimiva
    @21
    @9
    chil
    wcel
    #
    @13
    chil
    wcel
    #
    @26
    @14
    wb
    @20
    @1
    @54
    @56
    @55
    @8
    cT
    adjcl
    sylan2
    @1
    @18
    @19
    @57
    @1
    @18
    wa
    @36
    @37
    @57
    @1
    @19
    wa
    @40
    @41
    @11
    @12
    hvaddcl
    syl2an
    anandis
    vw
    @9
    @13
    hial2eq2
    syl2anc
    mpbid
    exp32
    ralrimdv
    ralrimivv
    vx
    vy
    vz
    @2
    ellnop
    sylanbrc
end
