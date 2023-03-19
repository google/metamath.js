include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "c2nd.mm"
include "cxp.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "xpcbas.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "eqidd.mm"
include "xpcval.mm"
include "catstr.mm"
include "homid.mm"
include "snsstp2.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "strfv3.mm"
include "wn.mm"
include "c0.mm"
include "mpt20.mm"
include "eqcomi.mm"
include "cxpc.mm"
include "wfn.mm"
include "cdm.mm"
include "fnxpc.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "str0.mm"
include "3eqtr4g.mm"
include "base0.mm"
include "mpt2eq123dv.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem xpchomfval
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cH: class H
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume xpchomfval.t: |- T = ( C Xc. D )
  assume xpchomfval.y: |- B = ( Base ` T )
  assume xpchomfval.h: |- H = ( Hom ` C )
  assume xpchomfval.j: |- J = ( Hom ` D )
  assume xpchomfval.k: |- K = ( Hom ` T )

  disjoint u v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  disjoint D u
  disjoint D v
  disjoint H u
  disjoint H v
  disjoint J u
  disjoint J v
  disjoint f g
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint X u
  disjoint X v
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint Y u
  disjoint Y v
  assert |- K = ( u e. B , v e. B |-> ( ( ( 1st ` u ) H ( 1st ` v ) ) X. ( ( 2nd ` u ) J ( 2nd ` v ) ) ) )

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
    cK
    vu
    vv
    cB
    cB
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
    cH
    co
    @3
    c2nd
    cfv
    @4
    c2nd
    cfv
    cJ
    co
    cxp
    #
    cmpt2
    #
    wceq
    @2
    cK
    @6
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    chom
    cfv
    #
    @6
    cop
    #
    cnx
    cco
    cfv
    vx
    vy
    cB
    cB
    cxp
    cB
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
    @6
    co
    @10
    @6
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
    @10
    c1st
    cfv
    #
    c1st
    cfv
    @11
    c1st
    cfv
    cop
    @12
    c1st
    cfv
    cC
    cco
    cfv
    #
    co
    co
    @13
    c2nd
    cfv
    @14
    c2nd
    cfv
    @15
    c2nd
    cfv
    @11
    c2nd
    cfv
    cop
    @12
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
    chom
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
    cB
    cC
    cD
    @17
    cT
    @16
    vf
    vg
    cH
    cJ
    @6
    @18
    cvv
    cvv
    cC
    cbs
    cfv
    #
    cD
    cbs
    cfv
    #
    xpchomfval.t
    @20
    eqid
    #
    @21
    eqid
    #
    xpchomfval.h
    xpchomfval.j
    @16
    eqid
    @17
    eqid
    @0
    @1
    simpl
    @0
    @1
    simpr
    cB
    @20
    @21
    cxp
    #
    wceq
    @2
    cB
    cT
    cbs
    cfv
    #
    @24
    xpchomfval.y
    cC
    cD
    cT
    @20
    @21
    xpchomfval.t
    @22
    @23
    xpcbas
    eqtr4i
    a1i
    @2
    @6
    eqidd
    @2
    @18
    eqidd
    xpcval
    @18
    cB
    @6
    catstr
    homid
    @7
    @9
    @19
    snsstp2
    @6
    cvv
    wcel
    @2
    vu
    vv
    cB
    cB
    @5
    cB
    @25
    cvv
    xpchomfval.y
    cT
    cbs
    fvex
    eqeltri
    #
    @26
    mpt2ex
    a1i
    xpchomfval.k
    strfv3
    @2
    wn
    #
    c0
    vu
    vv
    c0
    c0
    @5
    cmpt2
    #
    cK
    @6
    @28
    c0
    vu
    vv
    c0
    @5
    mpt20
    eqcomi
    @27
    cT
    chom
    cfv
    c0
    chom
    cfv
    cK
    c0
    @27
    cT
    c0
    chom
    @27
    cT
    cC
    cD
    cxpc
    co
    c0
    xpchomfval.t
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
    #
    fveq2d
    xpchomfval.k
    chom
    @8
    homid
    str0
    3eqtr4g
    @27
    vu
    vv
    cB
    cB
    @5
    c0
    c0
    @5
    @27
    @25
    c0
    cbs
    cfv
    cB
    c0
    @27
    cT
    c0
    cbs
    @30
    fveq2d
    xpchomfval.y
    base0
    3eqtr4g
    #
    @31
    @27
    @5
    eqidd
    mpt2eq123dv
    3eqtr4a
    pm2.61i
end
