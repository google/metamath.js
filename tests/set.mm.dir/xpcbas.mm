include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "chom.mm"
include "cv.mm"
include "c1st.mm"
include "co.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cco.mm"
include "ctp.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "eqidd.mm"
include "xpcval.mm"
include "catstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "a1i.mm"
include "strfv3.mm"
include "eqcomd.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "wo.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "orim12i.mm"
include "ianor.mm"
include "xpeq0.mm"
include "3imtr4i.mm"
include "cxpc.mm"
include "wfn.mm"
include "cdm.mm"
include "fnxpc.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem xpcbas
  let cC: class C
  let cD: class D
  let cT: class T
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume xpcbas.t: |- T = ( C Xc. D )
  assume xpcbas.x: |- X = ( Base ` C )
  assume xpcbas.y: |- Y = ( Base ` D )


  assert |- ( X X. Y ) = ( Base ` T )

  proof
    cC
    cvv
    wcel
    #
    cD
    cvv
    wcel
    #
    wa
    #
    cX
    cY
    cxp
    #
    cT
    cbs
    cfv
    #
    wceq
    @2
    @4
    @3
    @2
    @4
    @3
    cnx
    cbs
    cfv
    @3
    cop
    #
    cnx
    chom
    cfv
    vu
    vv
    @3
    @3
    vu
    cv
    #
    c1st
    cfv
    vv
    cv
    #
    c1st
    cfv
    cC
    chom
    cfv
    #
    co
    @6
    c2nd
    cfv
    @7
    c2nd
    cfv
    cD
    chom
    cfv
    #
    co
    cxp
    cmpt2
    #
    cop
    #
    cnx
    cco
    cfv
    vx
    vy
    @3
    @3
    cxp
    @3
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    @10
    co
    @12
    @10
    cfv
    vg
    cv
    #
    c1st
    cfv
    vf
    cv
    #
    c1st
    cfv
    @12
    c1st
    cfv
    #
    c1st
    cfv
    @13
    c1st
    cfv
    cop
    @14
    c1st
    cfv
    cC
    cco
    cfv
    #
    co
    co
    @15
    c2nd
    cfv
    @16
    c2nd
    cfv
    @17
    c2nd
    cfv
    @13
    c2nd
    cfv
    cop
    @14
    c2nd
    cfv
    cD
    cco
    cfv
    #
    co
    co
    cop
    cmpt2
    cmpt2
    #
    cop
    #
    ctp
    cT
    cbs
    cvv
    c1
    c1
    c5
    cdc
    cop
    @2
    vx
    vy
    vv
    vu
    @3
    cC
    cD
    @19
    cT
    @18
    vf
    vg
    @8
    @9
    @10
    @20
    cvv
    cvv
    cX
    cY
    xpcbas.t
    xpcbas.x
    xpcbas.y
    @8
    eqid
    @9
    eqid
    @18
    eqid
    @19
    eqid
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    @3
    eqidd
    @2
    @10
    eqidd
    @2
    @20
    eqidd
    xpcval
    @20
    @3
    @10
    catstr
    baseid
    @5
    @11
    @21
    snsstp1
    @3
    cvv
    wcel
    @2
    cX
    cY
    cX
    cC
    cbs
    cfv
    #
    cvv
    xpcbas.x
    cC
    cbs
    fvex
    eqeltri
    cY
    cD
    cbs
    cfv
    #
    cvv
    xpcbas.y
    cD
    cbs
    fvex
    eqeltri
    xpex
    a1i
    @4
    eqid
    strfv3
    eqcomd
    @2
    wn
    #
    c0
    c0
    cbs
    cfv
    @3
    @4
    base0
    @0
    wn
    #
    @1
    wn
    #
    wo
    cX
    c0
    wceq
    #
    cY
    c0
    wceq
    #
    wo
    @24
    @3
    c0
    wceq
    @25
    @27
    @26
    @28
    @25
    cX
    @22
    c0
    xpcbas.x
    cC
    cbs
    fvprc
    syl5eq
    @26
    cY
    @23
    c0
    xpcbas.y
    cD
    cbs
    fvprc
    syl5eq
    orim12i
    @0
    @1
    ianor
    cX
    cY
    xpeq0
    3imtr4i
    @24
    cT
    c0
    cbs
    @24
    cT
    cC
    cD
    cxpc
    co
    c0
    xpcbas.t
    cC
    cD
    cvv
    cxpc
    cxpc
    cvv
    cvv
    cxp
    #
    wfn
    cxpc
    cdm
    @29
    wceq
    fnxpc
    @29
    cxpc
    fndm
    ax-mp
    ndmov
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
