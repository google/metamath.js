include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cltrn.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "fvex.mm"
include "snex.mm"
include "xpex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "dibfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem dibfna
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vf: setvar f
  assume dibfna.h: |- H = ( LHyp ` K )
  assume dibfna.j: |- J = ( ( DIsoA ` K ) ` W )
  assume dibfna.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( K e. V /\ W e. H ) -> I Fn dom J )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    cJ
    cdm
    #
    wfn
    vy
    @1
    vy
    cv
    #
    cJ
    cfv
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    cmpt
    #
    csn
    #
    cxp
    #
    cmpt
    #
    @1
    wfn
    vy
    @1
    @8
    @9
    @3
    @7
    @2
    cJ
    fvex
    @6
    snex
    xpex
    @9
    eqid
    fnmpti
    @0
    @1
    cI
    @9
    vy
    @5
    @4
    vf
    cH
    cI
    cJ
    cK
    cV
    cW
    @6
    @5
    eqid
    dibfna.h
    @4
    eqid
    @6
    eqid
    dibfna.j
    dibfna.i
    dibfval
    fneq1d
    mpbiri
end
