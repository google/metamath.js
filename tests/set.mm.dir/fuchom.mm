include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "cfunc.mm"
include "co.mm"
include "cop.mm"
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
include "homid.mm"
include "snsstp2.mm"
include "cnat.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "strfv3.mm"
include "eqcomd.mm"
include "wn.mm"
include "c0.mm"
include "c4.mm"
include "df-hom.mm"
include "str0.mm"
include "wfn.mm"
include "cxp.mm"
include "natffn.mm"
include "cv.mm"
include "funcrcl.mm"
include "con3i.mm"
include "eq0rdv.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "fneq2d.mm"
include "mpbii.mm"
include "fn0.mm"
include "sylib.mm"
include "cfuc.mm"
include "cdm.mm"
include "fnfuc.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem fuchom
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  assume fucbas.q: |- Q = ( C FuncCat D )
  assume fuchom.n: |- N = ( C Nat D )


  assert |- N = ( Hom ` Q )

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
    cN
    cQ
    chom
    cfv
    #
    wceq
    @2
    @3
    cN
    @2
    @3
    cN
    cnx
    cbs
    cfv
    cC
    cD
    cfunc
    co
    #
    cop
    #
    cnx
    chom
    cfv
    cN
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
    chom
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
    @4
    cC
    cD
    cQ
    @7
    cD
    cco
    cfv
    #
    vf
    vg
    vh
    cN
    va
    vb
    fucbas.q
    @4
    eqid
    #
    fuchom.n
    @9
    eqid
    #
    @10
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
    @9
    @4
    cC
    cD
    cQ
    @7
    @10
    vf
    vg
    vh
    cN
    va
    vb
    fucbas.q
    @11
    fuchom.n
    @12
    @13
    @14
    @15
    @7
    eqid
    fuccofval
    fucval
    @7
    @4
    cN
    catstr
    homid
    @5
    @6
    @8
    snsstp2
    cN
    cvv
    wcel
    @2
    cN
    cC
    cD
    cnat
    co
    cvv
    fuchom.n
    cC
    cD
    cnat
    ovex
    eqeltri
    a1i
    @3
    eqid
    strfv3
    eqcomd
    @2
    wn
    #
    c0
    c0
    chom
    cfv
    cN
    @3
    chom
    c1
    c4
    cdc
    df-hom
    str0
    @16
    cN
    c0
    wfn
    #
    cN
    c0
    wceq
    @16
    cN
    @4
    @4
    cxp
    #
    wfn
    @17
    cC
    cD
    cN
    fuchom.n
    natffn
    @16
    @18
    c0
    cN
    @16
    @18
    @4
    c0
    cxp
    c0
    @16
    @4
    c0
    @4
    @16
    vf
    @4
    vf
    cv
    #
    @4
    wcel
    @2
    cC
    cD
    @19
    funcrcl
    con3i
    eq0rdv
    xpeq2d
    @4
    xp0
    syl6eq
    fneq2d
    mpbii
    cN
    fn0
    sylib
    @16
    cQ
    c0
    chom
    @16
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
