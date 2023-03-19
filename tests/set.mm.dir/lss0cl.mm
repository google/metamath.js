include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "lssn0.mm"
include "n0.mm"
include "sylib.mm"
include "adantl.mm"
include "w3a.mm"
include "csg.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "eqid.mm"
include "lssel.mm"
include "3adant1.mm"
include "lmodsubid.mm"
include "syl2anc.mm"
include "lssvsubcl.mm"
include "anabsan2.mm"
include "3impa.mm"
include "eqeltrrd.mm"
include "3expia.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem lss0cl
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let cX: class X
  let vy: setvar y
  assume lss0cl.z: |- .0. = ( 0g ` W )
  assume lss0cl.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ U e. S ) -> .0. e. U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    vx
    cv
    #
    cU
    wcel
    #
    vx
    wex
    #
    c.0
    cU
    wcel
    #
    @1
    @5
    @0
    @1
    cU
    c0
    wne
    @5
    cS
    cU
    cW
    lss0cl.s
    lssn0
    vx
    cU
    n0
    sylib
    adantl
    @2
    @4
    @6
    vx
    @0
    @1
    @4
    @6
    @0
    @1
    @4
    w3a
    #
    @3
    @3
    cW
    csg
    cfv
    #
    co
    #
    c.0
    cU
    @7
    @0
    @3
    cW
    cbs
    cfv
    #
    wcel
    #
    @9
    c.0
    wceq
    @0
    @1
    @4
    simp1
    @1
    @4
    @11
    @0
    cS
    cU
    @10
    cW
    @3
    @10
    eqid
    #
    lss0cl.s
    lssel
    3adant1
    @3
    @8
    @10
    cW
    c.0
    @12
    lss0cl.z
    @8
    eqid
    #
    lmodsubid
    syl2anc
    @0
    @1
    @4
    @9
    cU
    wcel
    #
    @2
    @4
    @14
    cS
    cU
    @8
    cW
    @3
    @3
    @13
    lss0cl.s
    lssvsubcl
    anabsan2
    3impa
    eqeltrrd
    3expia
    exlimdv
    mpd
end
