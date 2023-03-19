include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "crab.mm"
include "cglb.mm"
include "crn.mm"
include "cint.mm"
include "ccnv.mm"
include "eqid.mm"
include "dochval.mm"
include "wceq.mm"
include "ccla.mm"
include "hlclat.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "clatglbcl.mm"
include "sylancl.mm"
include "dihcnvid1.mm"
include "syldan.mm"
include "dihglb2.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "eqtrd.mm"

theorem dochval2
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume dochval2.o: |- ._|_ = ( oc ` K )
  assume dochval2.h: |- H = ( LHyp ` K )
  assume dochval2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochval2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochval2.v: |- V = ( Base ` U )
  assume dochval2.n: |- N = ( ( ocH ` K ) ` W )

  disjoint H z
  disjoint I z
  disjoint K z
  disjoint V z
  disjoint W z
  disjoint X z
  disjoint x z
  disjoint I x
  disjoint K x
  disjoint W x
  disjoint X x
  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V ) -> ( N ` X ) = ( I ` ( ._|_ ` ( `' I ` |^| { z e. ran I | X C_ z } ) ) ) )

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
    cN
    cfv
    cX
    vx
    cv
    cI
    cfv
    wss
    #
    vx
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
    c.pe
    cfv
    #
    cI
    cfv
    cX
    vz
    cv
    wss
    vz
    cI
    crn
    crab
    cint
    #
    cI
    ccnv
    #
    cfv
    #
    c.pe
    cfv
    #
    cI
    cfv
    vx
    @6
    cU
    @8
    cH
    cI
    cK
    cN
    c.pe
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
    dochval2.o
    dochval2.h
    dochval2.i
    dochval2.u
    dochval2.v
    dochval2.n
    dochval
    @4
    @10
    @14
    cI
    @4
    @9
    @13
    c.pe
    @4
    @9
    cI
    cfv
    #
    @12
    cfv
    #
    @9
    @13
    @2
    @3
    @9
    @6
    wcel
    #
    @18
    @9
    wceq
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
    vx
    @6
    ssrab2
    @6
    @7
    @8
    cK
    @15
    @16
    clatglbcl
    sylancl
    @6
    cH
    cI
    cK
    cW
    @9
    @15
    dochval2.h
    dochval2.i
    dihcnvid1
    syldan
    @4
    @17
    @11
    @12
    vx
    vz
    @6
    cX
    cU
    @8
    cH
    cI
    cK
    cV
    cW
    @15
    @16
    dochval2.h
    dochval2.i
    dochval2.u
    dochval2.v
    dihglb2
    fveq2d
    eqtr3d
    fveq2d
    fveq2d
    eqtrd
end
