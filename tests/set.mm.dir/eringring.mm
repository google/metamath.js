include "cbs.mm"
include "cfv.mm"
include "ctendo.mm"
include "cltrn.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "erngdvlem3.mm"

theorem eringring
  let cD: class D
  let cH: class H
  let cK: class K
  let cW: class W
  let cB: class B
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cI: class I
  let c.0: class .0.
  let cT: class T
  let cP: class P
  assume ernggrp.h: |- H = ( LHyp ` K )
  assume ernggrp.d: |- D = ( ( EDRing ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> D e. Ring )

  proof
    cK
    cbs
    cfv
    #
    cD
    va
    vb
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @1
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    vf
    cv
    #
    va
    cv
    #
    cfv
    #
    @3
    vb
    cv
    #
    cfv
    ccom
    cmpt
    cmpt2
    #
    va
    vb
    @1
    @1
    @4
    @6
    ccom
    cmpt2
    #
    @2
    vf
    @1
    cH
    va
    @1
    vf
    @2
    @5
    ccnv
    cmpt
    cmpt
    #
    cK
    cW
    vf
    @2
    cid
    @0
    cres
    cmpt
    #
    va
    vb
    ernggrp.h
    ernggrp.d
    @0
    eqid
    @2
    eqid
    @1
    eqid
    @7
    eqid
    @10
    eqid
    @9
    eqid
    @8
    eqid
    erngdvlem3
end
