include "cmnf.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cv.mm"
include "cpnf.mm"
include "cioc.mm"
include "cmpt.mm"
include "crn.mm"
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
include "ssun2.mm"
include "wceq.mm"
include "wrex.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "sseldi.mm"
include "adantl.mm"
include "wn.mm"
include "c0.mm"
include "cxp.mm"
include "cpw.mm"
include "clt.mm"
include "df-ico.mm"
include "ixxf.mm"
include "fdmi.mm"
include "ndmov.mm"
include "0opn.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem icomnfordt
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -oo [,) A ) e. ( ordTop ` <_ )

  proof
    cmnf
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    wa
    #
    cmnf
    cA
    cico
    co
    #
    cle
    cordt
    cfv
    #
    wcel
    #
    @1
    @5
    @0
    @1
    vx
    cxr
    vx
    cv
    #
    cpnf
    cioc
    co
    cmpt
    crn
    #
    vx
    cxr
    cmnf
    @6
    cico
    co
    #
    cmpt
    #
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
    @7
    @10
    @12
    @7
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
    @1
    @11
    @13
    @3
    @11
    @12
    ssun1
    @1
    @10
    @11
    @3
    @10
    @7
    ssun2
    @1
    @3
    @8
    wceq
    #
    vx
    cxr
    wrex
    #
    @3
    @10
    wcel
    @1
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
    @8
    @3
    @3
    @6
    cA
    cmnf
    cico
    oveq2
    eqeq2d
    rspcev
    mpan2
    vx
    cxr
    @8
    @3
    @9
    @9
    eqid
    cmnf
    @6
    cico
    ovex
    elrnmpti
    sylibr
    sseldi
    sseldi
    sseldi
    adantl
    @2
    wn
    @3
    c0
    @4
    cmnf
    cA
    cxr
    cico
    cxr
    cxr
    cxp
    cxr
    cpw
    cico
    vx
    vy
    vz
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
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
