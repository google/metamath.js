include "cgr.mm"
include "wcel.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "co.mm"
include "cgi.mm"
include "crio.mm"
include "cmpt.mm"
include "riotaex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "grpoinvfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "wrex.mm"
include "cab.mm"
include "fnrnfv.mm"
include "syl.mm"
include "wa.mm"
include "grpoinvcl.mm"
include "grpo2inv.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "abbi2dv.mm"
include "eqtr4d.mm"
include "wb.mm"
include "eqeqan12d.mm"
include "anandis.mm"
include "syl5ib.mm"
include "ralrimivva.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem grpoinvf
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpasscan1.1: |- X = ran G
  assume grpasscan1.2: |- N = ( inv ` G )


  assert |- ( G e. GrpOp -> N : X -1-1-onto-> X )

  proof
    cG
    cgr
    wcel
    #
    cN
    cX
    wfn
    #
    cN
    crn
    #
    cX
    wceq
    vx
    cv
    #
    cN
    cfv
    #
    vy
    cv
    #
    cN
    cfv
    #
    wceq
    #
    @3
    @5
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    cX
    cX
    cN
    wf1o
    @0
    @1
    vx
    cX
    @5
    @3
    cG
    co
    cG
    cgi
    cfv
    #
    wceq
    #
    vy
    cX
    crio
    #
    cmpt
    #
    cX
    wfn
    vx
    cX
    @12
    @13
    @11
    vy
    cX
    riotaex
    @13
    eqid
    fnmpti
    @0
    cX
    cN
    @13
    vx
    vy
    @10
    cG
    cN
    cX
    grpasscan1.1
    @10
    eqid
    grpasscan1.2
    grpoinvfval
    fneq1d
    mpbiri
    #
    @0
    @2
    @5
    @4
    wceq
    #
    vx
    cX
    wrex
    #
    vy
    cab
    #
    cX
    @0
    @1
    @2
    @17
    wceq
    @14
    vx
    vy
    cX
    cN
    fnrnfv
    syl
    @0
    @16
    vy
    cX
    @0
    @5
    cX
    wcel
    #
    @16
    @0
    @18
    @16
    @0
    @18
    wa
    #
    @6
    cX
    wcel
    @5
    @6
    cN
    cfv
    #
    wceq
    #
    @16
    @5
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpoinvcl
    @19
    @20
    @5
    @5
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpo2inv
    #
    eqcomd
    @15
    @21
    vx
    @6
    cX
    @3
    @6
    wceq
    @4
    @20
    @5
    @3
    @6
    cN
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ex
    @0
    @15
    @18
    vx
    cX
    @0
    @3
    cX
    wcel
    #
    @15
    @18
    @0
    @23
    wa
    #
    @15
    wa
    @5
    @4
    cX
    @24
    @15
    simpr
    @24
    @4
    cX
    wcel
    @15
    @3
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpoinvcl
    adantr
    eqeltrd
    exp31
    rexlimdv
    impbid
    abbi2dv
    eqtr4d
    @0
    @9
    vx
    vy
    cX
    cX
    @7
    @4
    cN
    cfv
    #
    @20
    wceq
    #
    @0
    @23
    @18
    wa
    wa
    @8
    @4
    @6
    cN
    fveq2
    @0
    @23
    @18
    @26
    @8
    wb
    @24
    @19
    @25
    @3
    @20
    @5
    @3
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpo2inv
    @22
    eqeqan12d
    anandis
    syl5ib
    ralrimivva
    vx
    vy
    cX
    cX
    cN
    dff1o6
    syl3anbrc
end
