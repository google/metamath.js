include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "cfunc.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "chom.mm"
include "cnat.mm"
include "cco.mm"
include "ctp.mm"
include "cvv.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "fuccofval.mm"
include "fucval.mm"
include "catstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "ovexd.mm"
include "strfv3.mm"
include "eqcomd.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "cv.mm"
include "funcrcl.mm"
include "con3i.mm"
include "eq0rdv.mm"
include "cfuc.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "fnfuc.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem fucbas
  let cC: class C
  let cD: class D
  let cQ: class Q
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  assume fucbas.q: |- Q = ( C FuncCat D )


  assert |- ( C Func D ) = ( Base ` Q )

  proof
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    wa
    #
    cC
    cD
    cfunc
    co
    #
    cQ
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
    cC
    cD
    cnat
    co
    #
    cop
    #
    cnx
    cco
    cfv
    cQ
    cco
    cfv
    #
    cop
    #
    ctp
    cQ
    cbs
    cvv
    c1
    c1
    c5
    cdc
    cop
    @2
    vx
    vv
    cC
    cbs
    cfv
    #
    @3
    cC
    cD
    cQ
    @8
    cD
    cco
    cfv
    #
    vf
    vg
    vh
    @6
    va
    vb
    fucbas.q
    @3
    eqid
    #
    @6
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    vx
    vv
    @10
    @3
    cC
    cD
    cQ
    @8
    @11
    vf
    vg
    vh
    @6
    va
    vb
    fucbas.q
    @12
    @13
    @14
    @15
    @16
    @17
    @8
    eqid
    fuccofval
    fucval
    @8
    @3
    @6
    catstr
    baseid
    @5
    @7
    @9
    snsstp1
    @2
    cC
    cD
    cfunc
    ovexd
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
    @18
    vf
    @3
    vf
    cv
    #
    @3
    wcel
    @2
    cC
    cD
    @19
    funcrcl
    con3i
    eq0rdv
    @18
    cQ
    c0
    cbs
    @18
    cQ
    cC
    cD
    cfuc
    co
    c0
    fucbas.q
    cC
    cD
    ccat
    cfuc
    cfuc
    ccat
    ccat
    cxp
    #
    wfn
    cfuc
    cdm
    @20
    wceq
    fnfuc
    @20
    cfuc
    fndm
    ax-mp
    ndmov
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
