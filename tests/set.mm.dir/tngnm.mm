include "cgrp.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "c0g.mm"
include "csg.mm"
include "ccom.mm"
include "co.mm"
include "cnm.mm"
include "simpr.mm"
include "feqmptd.mm"
include "cop.mm"
include "cxp.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubf.mm"
include "ad2antrr.mm"
include "grpidcl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fvco3.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "grpsubid1.mm"
include "adantlr.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "cbs.mm"
include "cds.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex2.mm"
include "mp3an23.mm"
include "adantl.mm"
include "tngbas.mm"
include "syl.mm"
include "tngds.mm"
include "eqidd.mm"
include "tng0.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "nmfval.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"

theorem tngnm
  let cA: class A
  let cT: class T
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  assume tngnm.t: |- T = ( G toNrmGrp N )
  assume tngnm.x: |- X = ( Base ` G )
  assume tngnm.a: |- A e. _V


  assert |- ( ( G e. Grp /\ N : X --> A ) -> N = ( norm ` T ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cA
    cN
    wf
    #
    wa
    #
    cN
    vx
    cX
    vx
    cv
    #
    cN
    cfv
    #
    cmpt
    vx
    cX
    @3
    cG
    c0g
    cfv
    #
    cN
    cG
    csg
    cfv
    #
    ccom
    #
    co
    #
    cmpt
    #
    cT
    cnm
    cfv
    #
    @2
    vx
    cX
    cA
    cN
    @0
    @1
    simpr
    feqmptd
    @2
    vx
    cX
    @4
    @8
    @2
    @3
    cX
    wcel
    #
    wa
    #
    @8
    @3
    @5
    @6
    co
    #
    cN
    cfv
    #
    @4
    @12
    @3
    @5
    cop
    #
    @7
    cfv
    #
    @15
    @6
    cfv
    #
    cN
    cfv
    #
    @8
    @14
    @12
    cX
    cX
    cxp
    #
    cX
    @6
    wf
    #
    @15
    @19
    wcel
    #
    @16
    @18
    wceq
    @0
    @20
    @1
    @11
    cX
    cG
    @6
    tngnm.x
    @6
    eqid
    #
    grpsubf
    ad2antrr
    @12
    @11
    @5
    cX
    wcel
    #
    @21
    @2
    @11
    simpr
    @0
    @23
    @1
    @11
    cX
    cG
    @5
    tngnm.x
    @5
    eqid
    #
    grpidcl
    ad2antrr
    @3
    @5
    cX
    cX
    opelxpi
    syl2anc
    @19
    cX
    @15
    cN
    @6
    fvco3
    syl2anc
    @3
    @5
    @7
    df-ov
    @13
    @17
    cN
    @3
    @5
    @6
    df-ov
    fveq2i
    3eqtr4g
    @12
    @13
    @3
    cN
    @0
    @11
    @13
    @3
    wceq
    @1
    cX
    cG
    @6
    @3
    @5
    tngnm.x
    @24
    @22
    grpsubid1
    adantlr
    fveq2d
    eqtr2d
    mpteq2dva
    @2
    @9
    vx
    cT
    cbs
    cfv
    #
    @3
    cT
    c0g
    cfv
    #
    cT
    cds
    cfv
    #
    co
    #
    cmpt
    @10
    @2
    vx
    cX
    @8
    @25
    @28
    @2
    cN
    cvv
    wcel
    #
    cX
    @25
    wceq
    @1
    @29
    @0
    @1
    cX
    cvv
    wcel
    cA
    cvv
    wcel
    @29
    cX
    cG
    cbs
    cfv
    cvv
    tngnm.x
    cG
    cbs
    fvex
    eqeltri
    tngnm.a
    cX
    cA
    cN
    cvv
    cvv
    fex2
    mp3an23
    adantl
    #
    cX
    cT
    cG
    cN
    cvv
    tngnm.t
    tngnm.x
    tngbas
    syl
    @2
    @3
    @3
    @5
    @26
    @7
    @27
    @2
    @29
    @7
    @27
    wceq
    @30
    cT
    cG
    @6
    cN
    cvv
    tngnm.t
    @22
    tngds
    syl
    @2
    @3
    eqidd
    @2
    @29
    @5
    @26
    wceq
    @30
    cT
    cG
    cN
    cvv
    @5
    tngnm.t
    @24
    tng0
    syl
    oveq123d
    mpteq12dv
    vx
    @27
    @10
    cT
    @25
    @26
    @10
    eqid
    @25
    eqid
    @26
    eqid
    @27
    eqid
    nmfval
    syl6eqr
    3eqtrd
end
