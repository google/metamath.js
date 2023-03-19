include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "syl6bb.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "crab.mm"
include "crn.mm"
include "cres.mm"
include "cxp.mm"
include "cin.mm"
include "cnvin.mm"
include "cnvxp.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "pjfval.mm"
include "cnveqi.mm"
include "df-res.mm"
include "3eqtr4i.mm"
include "rneqi.mm"
include "dfdm4.mm"
include "df-ima.mm"
include "eqid.mm"
include "mptpreima.mm"
include "elrab2.mm"

theorem pjdm
  let cP: class P
  let cT: class T
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vb: setvar b
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assume pjfval.v: |- V = ( Base ` W )
  assume pjfval.l: |- L = ( LSubSp ` W )
  assume pjfval.o: |- ._|_ = ( ocv ` W )
  assume pjfval.p: |- P = ( proj1 ` W )
  assume pjfval.k: |- K = ( proj ` W )


  assert |- ( T e. dom K <-> ( T e. L /\ ( T P ( ._|_ ` T ) ) : V --> V ) )

  proof
    vx
    cv
    #
    @0
    c.pe
    cfv
    #
    cP
    co
    #
    cV
    cV
    cmap
    co
    #
    wcel
    #
    cV
    cV
    cT
    cT
    c.pe
    cfv
    #
    cP
    co
    #
    wf
    #
    vx
    cT
    cL
    cK
    cdm
    #
    @0
    cT
    wceq
    #
    @4
    @6
    @3
    wcel
    @7
    @9
    @2
    @6
    @3
    @9
    @0
    cT
    @1
    @5
    cP
    @9
    id
    @0
    cT
    c.pe
    fveq2
    oveq12d
    eleq1d
    cV
    cV
    @6
    cV
    cW
    cbs
    cfv
    cvv
    pjfval.v
    cW
    cbs
    fvex
    eqeltri
    #
    @10
    elmap
    syl6bb
    @8
    vx
    cL
    @2
    cmpt
    #
    ccnv
    #
    @3
    cima
    #
    @4
    vx
    cL
    crab
    cK
    ccnv
    #
    crn
    @12
    @3
    cres
    #
    crn
    @8
    @13
    @14
    @15
    @11
    cvv
    @3
    cxp
    #
    cin
    #
    ccnv
    #
    @12
    @3
    cvv
    cxp
    #
    cin
    #
    @14
    @15
    @18
    @12
    @16
    ccnv
    #
    cin
    @20
    @11
    @16
    cnvin
    @21
    @19
    @12
    cvv
    @3
    cnvxp
    ineq2i
    eqtri
    cK
    @17
    vx
    cP
    cK
    cL
    c.pe
    cV
    cW
    pjfval.v
    pjfval.l
    pjfval.o
    pjfval.p
    pjfval.k
    pjfval
    cnveqi
    @12
    @3
    df-res
    3eqtr4i
    rneqi
    cK
    dfdm4
    @12
    @3
    df-ima
    3eqtr4i
    vx
    cL
    @2
    @3
    @11
    @11
    eqid
    mptpreima
    eqtri
    elrab2
end
