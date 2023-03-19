include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cmnf.mm"
include "cico.mm"
include "cun.mm"
include "cioo.mm"
include "ctg.mm"
include "ctb.mm"
include "wss.mm"
include "ctop.mm"
include "eqid.mm"
include "leordtval.mm"
include "letop.mm"
include "eqeltrri.mm"
include "tgclb.mm"
include "mpbir.mm"
include "bastg.mm"
include "ax-mp.mm"
include "sseqtr4i.mm"
include "ssun1.mm"
include "wceq.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "sseldi.mm"
include "adantr.mm"
include "wn.mm"
include "c0.mm"
include "cxp.mm"
include "cpw.mm"
include "clt.mm"
include "df-ioc.mm"
include "ixxf.mm"
include "fdmi.mm"
include "ndmov.mm"
include "0opn.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem iocpnfordt
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A (,] +oo ) e. ( ordTop ` <_ )

  proof
    cA
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    wa
    #
    cA
    cpnf
    cioc
    co
    #
    cle
    cordt
    cfv
    #
    wcel
    #
    @0
    @5
    @1
    @0
    vx
    cxr
    vx
    cv
    #
    cpnf
    cioc
    co
    #
    cmpt
    #
    crn
    #
    vx
    cxr
    cmnf
    @6
    cico
    co
    cmpt
    crn
    #
    cun
    #
    cioo
    crn
    #
    cun
    #
    @4
    @3
    @13
    @13
    ctg
    cfv
    #
    @4
    @13
    ctb
    wcel
    #
    @13
    @14
    wss
    @15
    @14
    ctop
    wcel
    @4
    @14
    ctop
    vx
    @9
    @10
    @12
    @9
    eqid
    @10
    eqid
    @12
    eqid
    leordtval
    #
    letop
    eqeltrri
    @13
    tgclb
    mpbir
    @13
    ctb
    bastg
    ax-mp
    @16
    sseqtr4i
    @0
    @11
    @13
    @3
    @11
    @12
    ssun1
    @0
    @9
    @11
    @3
    @9
    @10
    ssun1
    @0
    @3
    @7
    wceq
    #
    vx
    cxr
    wrex
    #
    @3
    @9
    wcel
    @0
    @3
    @3
    wceq
    #
    @18
    @3
    eqid
    @17
    @19
    vx
    cA
    cxr
    @6
    cA
    wceq
    @7
    @3
    @3
    @6
    cA
    cpnf
    cioc
    oveq1
    eqeq2d
    rspcev
    mpan2
    vx
    cxr
    @7
    @3
    @8
    @8
    eqid
    @6
    cpnf
    cioc
    ovex
    elrnmpti
    sylibr
    sseldi
    sseldi
    sseldi
    adantr
    @2
    wn
    @3
    c0
    @4
    cA
    cpnf
    cxr
    cioc
    cxr
    cxr
    cxp
    cxr
    cpw
    cioc
    vx
    vy
    vz
    clt
    cle
    cioc
    vx
    vy
    vz
    df-ioc
    ixxf
    fdmi
    ndmov
    @4
    ctop
    wcel
    c0
    @4
    wcel
    letop
    @4
    0opn
    ax-mp
    syl6eqel
    pm2.61i
end
