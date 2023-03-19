include "ccrg.mm"
include "wcel.mm"
include "cfv.mm"
include "c1o.mm"
include "cevl.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cmap.mm"
include "c0.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "cpl1.mm"
include "cbs.mm"
include "wceq.mm"
include "crg.mm"
include "crngring.mm"
include "eqid.mm"
include "vr1cl.mm"
include "syl.mm"
include "cmpl.mm"
include "cps1.mm"
include "ply1bas.mm"
include "evl1val.mm"
include "mpdan.mm"
include "df1o2.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "0ex.mm"
include "mapsncnv.mm"
include "coeq2i.mm"
include "cress.mm"
include "cmvr.mm"
include "ressid.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "vr1val.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "con0.mm"
include "evlval.mm"
include "1on.mm"
include "a1i.mm"
include "id.mm"
include "csubrg.mm"
include "subrgid.mm"
include "0lt1o.mm"
include "evlsvar.mm"
include "eqtr3d.mm"
include "coeq1d.mm"
include "syl5eqr.mm"
include "wf1o.mm"
include "mapsnf1o2.mm"
include "f1ococnv2.mm"
include "mp1i.mm"
include "3eqtrd.mm"

theorem evl1var
  let cB: class B
  let cR: class R
  let cO: class O
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume evl1var.q: |- O = ( eval1 ` R )
  assume evl1var.v: |- X = ( var1 ` R )
  assume evl1var.b: |- B = ( Base ` R )


  assert |- ( R e. CRing -> ( O ` X ) = ( _I |` B ) )

  proof
    cR
    ccrg
    wcel
    #
    cX
    cO
    cfv
    #
    cX
    c1o
    cR
    cevl
    co
    #
    cfv
    #
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    vz
    cB
    c1o
    cmap
    co
    #
    c0
    vz
    cv
    cfv
    cmpt
    #
    @7
    ccnv
    #
    ccom
    #
    cid
    cB
    cres
    #
    @0
    cX
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @1
    @5
    wceq
    @0
    cR
    crg
    wcel
    #
    @13
    cR
    crngring
    #
    @12
    @11
    cR
    cX
    evl1var.v
    @11
    eqid
    #
    @12
    eqid
    #
    vr1cl
    syl
    vy
    cX
    cB
    @2
    cR
    @12
    c1o
    cR
    cmpl
    co
    #
    cO
    evl1var.q
    @2
    eqid
    #
    evl1var.b
    @18
    eqid
    @11
    cR
    cR
    cps1
    cfv
    #
    @12
    @16
    @20
    eqid
    @17
    ply1bas
    evl1val
    mpdan
    @0
    @5
    @3
    @8
    ccom
    @9
    @8
    @4
    @3
    vz
    vy
    cB
    c1o
    @7
    c0
    df1o2
    cB
    cR
    cbs
    cfv
    cvv
    evl1var.b
    cR
    cbs
    fvex
    eqeltri
    #
    0ex
    @7
    eqid
    #
    mapsncnv
    coeq2i
    @0
    @3
    @7
    @8
    @0
    c0
    c1o
    cR
    cB
    cress
    co
    #
    cmvr
    co
    #
    cfv
    #
    @2
    cfv
    @3
    @7
    @0
    @25
    cX
    @2
    @0
    @25
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    cX
    @0
    c0
    @24
    @26
    @0
    @23
    cR
    c1o
    cmvr
    cB
    cR
    ccrg
    evl1var.b
    ressid
    oveq2d
    fveq1d
    cR
    cX
    evl1var.v
    vr1val
    syl6eqr
    fveq2d
    @0
    cB
    @2
    cB
    cR
    @23
    vz
    c1o
    @24
    con0
    c0
    cB
    @2
    cR
    c1o
    @19
    evl1var.b
    evlval
    @24
    eqid
    @23
    eqid
    evl1var.b
    c1o
    con0
    wcel
    @0
    1on
    a1i
    @0
    id
    @0
    @14
    cB
    cR
    csubrg
    cfv
    wcel
    @15
    cB
    cR
    evl1var.b
    subrgid
    syl
    c0
    c1o
    wcel
    @0
    0lt1o
    a1i
    evlsvar
    eqtr3d
    coeq1d
    syl5eqr
    @6
    cB
    @7
    wf1o
    @9
    @10
    wceq
    @0
    vz
    cB
    c1o
    @7
    c0
    df1o2
    @21
    0ex
    @22
    mapsnf1o2
    @6
    cB
    @7
    f1ococnv2
    mp1i
    3eqtrd
end
