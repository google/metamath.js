include "cnop.mm"
include "cno.mm"
include "cv.mm"
include "c0v.mm"
include "cmv.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "wi.mm"
include "chil.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ccop.mm"
include "wcel.mm"
include "ax-hv0cl.mm"
include "1rp.mm"
include "cnopc.mm"
include "mp3an.mm"
include "hvsub0.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "lnop0i.mm"
include "oveq2i.mm"
include "wceq.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "syl.mm"
include "syl5eq.mm"
include "imbi12d.mm"
include "ralbiia.mm"
include "rexbii.mm"
include "mpbi.mm"
include "wf.mm"
include "cle.mm"
include "wa.mm"
include "cab.mm"
include "cxr.mm"
include "csup.mm"
include "nmopval.mm"
include "ax-mp.mm"
include "cr.mm"
include "normcl.mm"
include "cc0.mm"
include "fveq2i.mm"
include "norm0.mm"
include "eqtri.mm"
include "c2.mm"
include "cdiv.mm"
include "csm.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "rpcn.mm"
include "lnopmuli.mm"
include "sylan.mm"
include "norm-iii.mm"
include "syl2an.mm"
include "rpre.mm"
include "rpge0.mm"
include "absidd.mm"
include "adantr.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "nmcexi.mm"

theorem nmcopexi
  let cT: class T
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmcopex.1: |- T e. LinOp
  assume nmcopex.2: |- T e. ContOp


  assert |- ( normop ` T ) e. RR

  proof
    vx
    vy
    vz
    cnop
    cT
    vm
    cno
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
    cmv
    co
    #
    cno
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
    cno
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
    ccop
    wcel
    c0v
    chil
    wcel
    c1
    crp
    wcel
    @12
    nmcopex.2
    ax-hv0cl
    1rp
    vy
    vz
    c0v
    c1
    cT
    cnopc
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
    cno
    @19
    @7
    @5
    c0v
    cmv
    co
    #
    @5
    @6
    c0v
    @5
    cmv
    cT
    nmcopex.1
    lnop0i
    #
    oveq2i
    @19
    @5
    chil
    wcel
    @20
    @5
    wceq
    chil
    chil
    @0
    cT
    cT
    nmcopex.1
    lnopfi
    #
    ffvelrni
    @5
    hvsub0
    syl
    syl5eq
    fveq2d
    breq1d
    imbi12d
    ralbiia
    rexbii
    mpbi
    chil
    chil
    cT
    wf
    cT
    cnop
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
    @23
    cT
    cfv
    #
    cno
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
    @22
    vm
    vx
    cT
    nmopval
    ax-mp
    @23
    chil
    wcel
    #
    @24
    chil
    wcel
    #
    @25
    cr
    wcel
    chil
    chil
    @23
    cT
    @22
    ffvelrni
    #
    @24
    normcl
    syl
    @6
    cno
    cfv
    c0v
    cno
    cfv
    cc0
    @6
    c0v
    cno
    @21
    fveq2i
    norm0
    eqtri
    @3
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @26
    wa
    #
    @29
    @23
    csm
    co
    cT
    cfv
    #
    cno
    cfv
    @29
    @24
    csm
    co
    #
    cno
    cfv
    #
    @29
    cabs
    cfv
    #
    @25
    cmul
    co
    #
    @29
    @25
    cmul
    co
    @31
    @32
    @33
    cno
    @30
    @29
    cc
    wcel
    #
    @26
    @32
    @33
    wceq
    @29
    rpcn
    #
    @29
    @23
    cT
    nmcopex.1
    lnopmuli
    sylan
    fveq2d
    @30
    @37
    @27
    @34
    @36
    wceq
    @26
    @38
    @28
    @29
    @24
    norm-iii
    syl2an
    @31
    @35
    @29
    @25
    cmul
    @30
    @35
    @29
    wceq
    @26
    @30
    @29
    @29
    rpre
    @29
    rpge0
    absidd
    adantr
    oveq1d
    3eqtrrd
    nmcexi
end
