include "ccnfld.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cress.mm"
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
include "csubmnd.mm"
include "crg.mm"
include "cnring.mm"
include "ringcmn.mm"
include "ax-mp.mm"
include "rege0subm.mm"
include "eqid.mm"
include "submcmn.mm"
include "mp2an.mm"
include "cc.mm"
include "wss.mm"
include "c1.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "1re.mm"
include "0le1.mm"
include "ltpnf.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0re.mm"
include "pnfxr.mm"
include "elico2.mm"
include "mpbir3an.mm"
include "ge0mulcl.mm"
include "rgen2a.mm"
include "ringmgp.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "issubm.mm"
include "mp2b.mm"
include "submmnd.mm"
include "simpll.mm"
include "sseldi.mm"
include "simplr.mm"
include "simpr.mm"
include "adddid.mm"
include "adddird.mm"
include "jca.mm"
include "ralrimiva.mm"
include "sseli.mm"
include "mul02d.mm"
include "mul01d.mm"
include "jca32.mm"
include "rgen.mm"
include "cbs.mm"
include "ressbas2.mm"
include "cvv.mm"
include "cnfldex.mm"
include "ovex.mm"
include "mgpress.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "cmulr.mm"
include "ressmulr.mm"
include "c0g.mm"
include "ringmnd.mm"
include "0e0icopnf.mm"
include "cnfld0.mm"
include "ress0g.mm"
include "mp3an.mm"
include "issrg.mm"

theorem rge0srg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( CCfld |`s ( 0 [,) +oo ) ) e. SRing

  proof
    ccnfld
    cc0
    cpnf
    cico
    co
    #
    cress
    co
    #
    csrg
    wcel
    @1
    ccmn
    wcel
    #
    ccnfld
    cmgp
    cfv
    #
    @0
    cress
    co
    #
    cmnd
    wcel
    #
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
    @6
    @7
    cmul
    co
    #
    @6
    @8
    cmul
    co
    #
    caddc
    co
    wceq
    #
    @6
    @7
    caddc
    co
    @8
    cmul
    co
    @10
    @7
    @8
    cmul
    co
    caddc
    co
    wceq
    #
    wa
    #
    vz
    @0
    wral
    #
    vy
    @0
    wral
    #
    cc0
    @6
    cmul
    co
    cc0
    wceq
    #
    @6
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
    @0
    wral
    ccnfld
    ccmn
    wcel
    #
    @0
    ccnfld
    csubmnd
    cfv
    wcel
    @2
    ccnfld
    crg
    wcel
    #
    @19
    cnring
    ccnfld
    ringcmn
    ax-mp
    rege0subm
    @0
    ccnfld
    @1
    @1
    eqid
    #
    submcmn
    mp2an
    @0
    @3
    csubmnd
    cfv
    wcel
    #
    @5
    @22
    @0
    cc
    wss
    #
    c1
    @0
    wcel
    #
    @9
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @0
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    @24
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    c1
    cpnf
    clt
    wbr
    #
    1re
    0le1
    @28
    @30
    1re
    c1
    ltpnf
    ax-mp
    cc0
    cr
    wcel
    cpnf
    cxr
    wcel
    @24
    @28
    @29
    @30
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    c1
    elico2
    mp2an
    mpbir3an
    @25
    vx
    vy
    @0
    @6
    @7
    ge0mulcl
    rgen2a
    @20
    @3
    cmnd
    wcel
    @22
    @23
    @24
    @26
    w3a
    wb
    cnring
    ccnfld
    @3
    @3
    eqid
    #
    ringmgp
    vx
    vy
    cc
    cmul
    @0
    @3
    c1
    cc
    ccnfld
    @3
    @31
    cnfldbas
    mgpbas
    ccnfld
    c1
    @3
    @31
    cnfld1
    ringidval
    ccnfld
    cmul
    @3
    @31
    cnfldmul
    mgpplusg
    issubm
    mp2b
    mpbir3an
    @0
    @4
    @3
    @4
    eqid
    submmnd
    ax-mp
    @18
    vx
    @0
    @6
    @0
    wcel
    #
    @15
    @16
    @17
    @32
    @14
    vy
    @0
    @32
    @7
    @0
    wcel
    #
    wa
    #
    @13
    vz
    @0
    @34
    @8
    @0
    wcel
    #
    wa
    #
    @11
    @12
    @36
    @6
    @7
    @8
    @36
    @0
    cc
    @6
    @27
    @32
    @33
    @35
    simpll
    sseldi
    #
    @36
    @0
    cc
    @7
    @27
    @32
    @33
    @35
    simplr
    sseldi
    #
    @36
    @0
    cc
    @8
    @27
    @34
    @35
    simpr
    sseldi
    #
    adddid
    @36
    @6
    @7
    @8
    @37
    @38
    @39
    adddird
    jca
    ralrimiva
    ralrimiva
    @32
    @6
    @0
    cc
    @6
    @27
    sseli
    #
    mul02d
    @32
    @6
    @40
    mul01d
    jca32
    rgen
    vx
    vy
    vz
    @0
    caddc
    @1
    cmul
    @4
    cc0
    @23
    @0
    @1
    cbs
    cfv
    wceq
    @27
    @0
    cc
    @1
    ccnfld
    @21
    cnfldbas
    ressbas2
    ax-mp
    ccnfld
    cvv
    wcel
    @0
    cvv
    wcel
    #
    @4
    @1
    cmgp
    cfv
    wceq
    cnfldex
    cc0
    cpnf
    cico
    ovex
    #
    @0
    ccnfld
    @1
    @3
    cvv
    cvv
    @21
    @31
    mgpress
    mp2an
    @41
    caddc
    @1
    cplusg
    cfv
    wceq
    @42
    @0
    caddc
    ccnfld
    @1
    cvv
    @21
    cnfldadd
    ressplusg
    ax-mp
    @41
    cmul
    @1
    cmulr
    cfv
    wceq
    @42
    @0
    ccnfld
    @1
    cmul
    cvv
    @21
    cnfldmul
    ressmulr
    ax-mp
    ccnfld
    cmnd
    wcel
    #
    cc0
    @0
    wcel
    @23
    cc0
    @1
    c0g
    cfv
    wceq
    @20
    @43
    cnring
    ccnfld
    ringmnd
    ax-mp
    0e0icopnf
    @27
    @0
    cc
    ccnfld
    @1
    cc0
    @21
    cnfldbas
    cnfld0
    ress0g
    mp3an
    issrg
    mpbir3an
end
