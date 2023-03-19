include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "wrel.mm"
include "cdia.mm"
include "cltrn.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "relxp.mm"
include "wceq.mm"
include "eqid.mm"
include "dibdiadm.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "dibval.mm"
include "syldan.mm"
include "releqd.mm"
include "mpbiri.mm"
include "wn.mm"
include "c0.mm"
include "rel0.mm"
include "ndmfv.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem dibvalrel
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  assume dibcl.h: |- H = ( LHyp ` K )
  assume dibcl.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( K e. V /\ W e. H ) -> Rel ( I ` X ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    cdm
    #
    wcel
    #
    cX
    cI
    cfv
    #
    wrel
    #
    @0
    @2
    wa
    #
    @4
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    vh
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
    wrel
    @7
    @11
    relxp
    @5
    @3
    @12
    @0
    @2
    cX
    @6
    cdm
    #
    wcel
    #
    @3
    @12
    wceq
    @0
    @2
    @14
    @0
    @1
    @13
    cX
    cH
    cI
    @6
    cK
    cV
    cW
    dibcl.h
    @6
    eqid
    #
    dibcl.i
    dibdiadm
    eleq2d
    biimpa
    @9
    @8
    vh
    cH
    cI
    @6
    cK
    cV
    cW
    cX
    @10
    @9
    eqid
    dibcl.h
    @8
    eqid
    @10
    eqid
    @15
    dibcl.i
    dibval
    syldan
    releqd
    mpbiri
    @2
    wn
    #
    @4
    @0
    @16
    @4
    c0
    wrel
    rel0
    @16
    @3
    c0
    cX
    cI
    ndmfv
    releqd
    mpbiri
    adantl
    pm2.61dan
end
