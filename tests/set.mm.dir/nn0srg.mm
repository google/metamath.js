include "ccnfld.mm"
include "cn0.mm"
include "cress.mm"
include "co.mm"
include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cc0.mm"
include "csubmnd.mm"
include "crg.mm"
include "cnring.mm"
include "ringcmn.mm"
include "ax-mp.mm"
include "nn0subm.mm"
include "eqid.mm"
include "submcmn.mm"
include "mp2an.mm"
include "cvv.mm"
include "nn0ex.mm"
include "mgpress.mm"
include "cc.mm"
include "wss.mm"
include "c1.mm"
include "nn0sscn.mm"
include "1nn0.mm"
include "nn0mulcl.mm"
include "rgen2a.mm"
include "w3a.mm"
include "wb.mm"
include "ringmgp.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "issubm.mm"
include "mpbir3an.mm"
include "submmnd.mm"
include "eqeltrri.mm"
include "simpl.mm"
include "nn0cnd.mm"
include "simprl.mm"
include "simprr.mm"
include "adddid.mm"
include "adddird.mm"
include "jca.mm"
include "ralrimivva.mm"
include "nn0cn.mm"
include "mul02d.mm"
include "mul01d.mm"
include "jca32.mm"
include "rgen.mm"
include "cbs.mm"
include "ressbas2.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "cmulr.mm"
include "ressmulr.mm"
include "c0g.mm"
include "ringmnd.mm"
include "0nn0.mm"
include "cnfld0.mm"
include "ress0g.mm"
include "mp3an.mm"
include "issrg.mm"

theorem nn0srg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( CCfld |`s NN0 ) e. SRing

  proof
    ccnfld
    cn0
    cress
    co
    #
    csrg
    wcel
    @0
    ccmn
    wcel
    #
    @0
    cmgp
    cfv
    #
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    caddc
    co
    cmul
    co
    @3
    @4
    cmul
    co
    #
    @3
    @5
    cmul
    co
    #
    caddc
    co
    wceq
    #
    @3
    @4
    caddc
    co
    @5
    cmul
    co
    @7
    @4
    @5
    cmul
    co
    caddc
    co
    wceq
    #
    wa
    #
    vz
    cn0
    wral
    vy
    cn0
    wral
    #
    cc0
    @3
    cmul
    co
    cc0
    wceq
    #
    @3
    cc0
    cmul
    co
    cc0
    wceq
    #
    wa
    wa
    #
    vx
    cn0
    wral
    ccnfld
    ccmn
    wcel
    #
    cn0
    ccnfld
    csubmnd
    cfv
    wcel
    @1
    ccnfld
    crg
    wcel
    #
    @15
    cnring
    ccnfld
    ringcmn
    ax-mp
    #
    nn0subm
    cn0
    ccnfld
    @0
    @0
    eqid
    #
    submcmn
    mp2an
    ccnfld
    cmgp
    cfv
    #
    cn0
    cress
    co
    #
    @2
    cmnd
    @15
    cn0
    cvv
    wcel
    #
    @20
    @2
    wceq
    @17
    nn0ex
    cn0
    ccnfld
    @0
    @19
    ccmn
    cvv
    @18
    @19
    eqid
    #
    mgpress
    mp2an
    cn0
    @19
    csubmnd
    cfv
    wcel
    #
    @20
    cmnd
    wcel
    @23
    cn0
    cc
    wss
    #
    c1
    cn0
    wcel
    #
    @6
    cn0
    wcel
    #
    vy
    cn0
    wral
    vx
    cn0
    wral
    #
    nn0sscn
    1nn0
    @26
    vx
    vy
    cn0
    @3
    @4
    nn0mulcl
    rgen2a
    @19
    cmnd
    wcel
    #
    @23
    @24
    @25
    @27
    w3a
    wb
    @16
    @28
    cnring
    ccnfld
    @19
    @22
    ringmgp
    ax-mp
    vx
    vy
    cc
    cmul
    cn0
    @19
    c1
    cc
    ccnfld
    @19
    @22
    cnfldbas
    mgpbas
    ccnfld
    c1
    @19
    @22
    cnfld1
    ringidval
    ccnfld
    cmul
    @19
    @22
    cnfldmul
    mgpplusg
    issubm
    ax-mp
    mpbir3an
    cn0
    @20
    @19
    @20
    eqid
    submmnd
    ax-mp
    eqeltrri
    @14
    vx
    cn0
    @3
    cn0
    wcel
    #
    @11
    @12
    @13
    @29
    @10
    vy
    vz
    cn0
    cn0
    @29
    @4
    cn0
    wcel
    #
    @5
    cn0
    wcel
    #
    wa
    #
    wa
    #
    @8
    @9
    @33
    @3
    @4
    @5
    @33
    @3
    @29
    @32
    simpl
    nn0cnd
    #
    @33
    @4
    @29
    @30
    @31
    simprl
    nn0cnd
    #
    @33
    @5
    @29
    @30
    @31
    simprr
    nn0cnd
    #
    adddid
    @33
    @3
    @4
    @5
    @34
    @35
    @36
    adddird
    jca
    ralrimivva
    @29
    @3
    @3
    nn0cn
    #
    mul02d
    @29
    @3
    @37
    mul01d
    jca32
    rgen
    vx
    vy
    vz
    cn0
    caddc
    @0
    cmul
    @2
    cc0
    @24
    cn0
    @0
    cbs
    cfv
    wceq
    nn0sscn
    cn0
    cc
    @0
    ccnfld
    @18
    cnfldbas
    ressbas2
    ax-mp
    @2
    eqid
    @21
    caddc
    @0
    cplusg
    cfv
    wceq
    nn0ex
    cn0
    caddc
    ccnfld
    @0
    cvv
    @18
    cnfldadd
    ressplusg
    ax-mp
    @21
    cmul
    @0
    cmulr
    cfv
    wceq
    nn0ex
    cn0
    ccnfld
    @0
    cmul
    cvv
    @18
    cnfldmul
    ressmulr
    ax-mp
    ccnfld
    cmnd
    wcel
    #
    cc0
    cn0
    wcel
    @24
    cc0
    @0
    c0g
    cfv
    wceq
    @16
    @38
    cnring
    ccnfld
    ringmnd
    ax-mp
    0nn0
    nn0sscn
    cn0
    cc
    ccnfld
    @0
    cc0
    @18
    cnfldbas
    cnfld0
    ress0g
    mp3an
    issrg
    mpbir3an
end
