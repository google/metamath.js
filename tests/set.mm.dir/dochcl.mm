include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "crab.mm"
include "cglb.mm"
include "coc.mm"
include "crn.mm"
include "eqid.mm"
include "dochval.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "ccla.mm"
include "hlclat.mm"
include "ssrab2.mm"
include "clatglbcl.mm"
include "sylancl.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "dihcl.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem dochcl
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  assume dochcl.h: |- H = ( LHyp ` K )
  assume dochcl.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochcl.v: |- V = ( Base ` U )
  assume dochcl.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V ) -> ( ._|_ ` X ) e. ran I )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cV
    wss
    #
    wa
    #
    cX
    c.pe
    cfv
    cX
    vy
    cv
    cI
    cfv
    wss
    #
    vy
    cK
    cbs
    cfv
    #
    crab
    #
    cK
    cglb
    cfv
    #
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    cI
    crn
    #
    vy
    @6
    cU
    @8
    cH
    cI
    cK
    c.pe
    @10
    cV
    cW
    cX
    chlt
    @6
    eqid
    #
    @8
    eqid
    #
    @10
    eqid
    #
    dochcl.h
    dochcl.i
    dochcl.u
    dochcl.v
    dochcl.o
    dochval
    @2
    @3
    @11
    @6
    wcel
    #
    @12
    @13
    wcel
    @4
    cK
    cops
    wcel
    #
    @9
    @6
    wcel
    #
    @17
    @0
    @18
    @1
    @3
    cK
    hlop
    ad2antrr
    @4
    cK
    ccla
    wcel
    #
    @7
    @6
    wss
    @19
    @0
    @20
    @1
    @3
    cK
    hlclat
    ad2antrr
    @5
    vy
    @6
    ssrab2
    @6
    @7
    @8
    cK
    @14
    @15
    clatglbcl
    sylancl
    @6
    cK
    @10
    @9
    @14
    @16
    opoccl
    syl2anc
    @6
    cH
    cI
    cK
    cW
    @11
    @14
    dochcl.h
    dochcl.i
    dihcl
    syldan
    eqeltrd
end
