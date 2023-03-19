include "cal.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "crab.mm"
include "c0.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "atl0cl.mm"
include "pmapval.mm"
include "mpdan.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "atnle0.mm"
include "nrexdv.mm"
include "rabn0.mm"
include "sylnibr.mm"
include "nne.mm"
include "sylib.mm"
include "eqtrd.mm"

theorem pmap0
  let cK: class K
  let cM: class M
  let c.0: class .0.
  let va: setvar a
  assume pmap0.z: |- .0. = ( 0. ` K )
  assume pmap0.m: |- M = ( pmap ` K )


  assert |- ( K e. AtLat -> ( M ` .0. ) = (/) )

  proof
    cK
    cal
    wcel
    #
    c.0
    cM
    cfv
    #
    va
    cv
    #
    c.0
    cK
    cple
    cfv
    #
    wbr
    #
    va
    cK
    catm
    cfv
    #
    crab
    #
    c0
    @0
    c.0
    cK
    cbs
    cfv
    #
    wcel
    @1
    @6
    wceq
    @7
    cK
    c.0
    @7
    eqid
    #
    pmap0.z
    atl0cl
    @5
    @7
    cal
    cK
    @3
    cM
    c.0
    va
    @8
    @3
    eqid
    #
    @5
    eqid
    #
    pmap0.m
    pmapval
    mpdan
    @0
    @6
    c0
    wne
    #
    wn
    @6
    c0
    wceq
    @0
    @4
    va
    @5
    wrex
    @11
    @0
    @4
    va
    @5
    @5
    @2
    cK
    @3
    c.0
    @9
    pmap0.z
    @10
    atnle0
    nrexdv
    @4
    va
    @5
    rabn0
    sylnibr
    @6
    c0
    nne
    sylib
    eqtrd
end
