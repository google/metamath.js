include "cnmf.mm"
include "cabs.mm"
include "cv.mm"
include "c0v.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "c1.mm"
include "wi.mm"
include "chil.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ccnfn.mm"
include "wcel.mm"
include "ax-hv0cl.mm"
include "1rp.mm"
include "cnfnc.mm"
include "mp3an.mm"
include "hvsub0.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cc0.mm"
include "lnfn0i.mm"
include "oveq2i.mm"
include "cc.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "subid1d.mm"
include "syl5eq.mm"
include "imbi12d.mm"
include "ralbiia.mm"
include "rexbii.mm"
include "mpbi.mm"
include "wf.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "cxr.mm"
include "csup.mm"
include "nmfnval.mm"
include "ax-mp.mm"
include "abscld.mm"
include "fveq2i.mm"
include "abs0.mm"
include "eqtri.mm"
include "c2.mm"
include "cdiv.mm"
include "csm.mm"
include "cmul.mm"
include "rpcn.mm"
include "lnfnmuli.mm"
include "sylan.mm"
include "absmul.mm"
include "syl2an.mm"
include "rpre.mm"
include "rpge0.mm"
include "absidd.mm"
include "adantr.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "nmcexi.mm"

theorem nmcfnexi
  let cT: class T
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmcfnex.1: |- T e. LinFn
  assume nmcfnex.2: |- T e. ContFn


  assert |- ( normfn ` T ) e. RR

  proof
    vx
    vy
    vz
    cnmf
    cT
    vm
    cabs
    vz
    cv
    #
    c0v
    cmv
    co
    #
    cno
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @0
    cT
    cfv
    #
    c0v
    cT
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wi
    #
    vz
    chil
    wral
    #
    vy
    crp
    wrex
    #
    @0
    cno
    cfv
    #
    @3
    clt
    wbr
    #
    @5
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wi
    #
    vz
    chil
    wral
    #
    vy
    crp
    wrex
    cT
    ccnfn
    wcel
    c0v
    chil
    wcel
    c1
    crp
    wcel
    @12
    nmcfnex.2
    ax-hv0cl
    1rp
    vy
    vz
    c0v
    c1
    cT
    cnfnc
    mp3an
    @11
    @18
    vy
    crp
    @10
    @17
    vz
    chil
    @0
    chil
    wcel
    #
    @4
    @14
    @9
    @16
    @19
    @2
    @13
    @3
    clt
    @19
    @1
    @0
    cno
    @0
    hvsub0
    fveq2d
    breq1d
    @19
    @8
    @15
    c1
    clt
    @19
    @7
    @5
    cabs
    @19
    @7
    @5
    cc0
    cmin
    co
    @5
    @6
    cc0
    @5
    cmin
    cT
    nmcfnex.1
    lnfn0i
    #
    oveq2i
    @19
    @5
    chil
    cc
    @0
    cT
    cT
    nmcfnex.1
    lnfnfi
    #
    ffvelrni
    subid1d
    syl5eq
    fveq2d
    breq1d
    imbi12d
    ralbiia
    rexbii
    mpbi
    chil
    cc
    cT
    wf
    cT
    cnmf
    cfv
    vx
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    vm
    cv
    @22
    cT
    cfv
    #
    cabs
    cfv
    #
    wceq
    wa
    vx
    chil
    wrex
    vm
    cab
    cxr
    clt
    csup
    wceq
    @21
    vm
    vx
    cT
    nmfnval
    ax-mp
    @22
    chil
    wcel
    #
    @23
    chil
    cc
    @22
    cT
    @21
    ffvelrni
    #
    abscld
    @6
    cabs
    cfv
    cc0
    cabs
    cfv
    cc0
    @6
    cc0
    cabs
    @20
    fveq2i
    abs0
    eqtri
    @3
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @25
    wa
    #
    @27
    @22
    csm
    co
    cT
    cfv
    #
    cabs
    cfv
    @27
    @23
    cmul
    co
    #
    cabs
    cfv
    #
    @27
    cabs
    cfv
    #
    @24
    cmul
    co
    #
    @27
    @24
    cmul
    co
    @29
    @30
    @31
    cabs
    @28
    @27
    cc
    wcel
    #
    @25
    @30
    @31
    wceq
    @27
    rpcn
    #
    @27
    @22
    cT
    nmcfnex.1
    lnfnmuli
    sylan
    fveq2d
    @28
    @35
    @23
    cc
    wcel
    @32
    @34
    wceq
    @25
    @36
    @26
    @27
    @23
    absmul
    syl2an
    @29
    @33
    @27
    @24
    cmul
    @28
    @33
    @27
    wceq
    @25
    @28
    @27
    @27
    rpre
    @27
    rpge0
    absidd
    adantr
    oveq1d
    3eqtrrd
    nmcexi
end
