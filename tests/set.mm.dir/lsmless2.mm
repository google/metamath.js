include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cgrp.mm"
include "cbs.mm"
include "co.mm"
include "subgrcl.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "subgss.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "lsmless2x.mm"
include "syl31anc.mm"

theorem lsmless2
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let cR: class R
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) /\ T C_ U ) -> ( S .(+) T ) C_ ( S .(+) U ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cT
    cU
    wss
    #
    w3a
    cG
    cgrp
    wcel
    #
    cS
    cG
    cbs
    cfv
    #
    wss
    #
    cU
    @5
    wss
    #
    @3
    cS
    cT
    c.po
    co
    cS
    cU
    c.po
    co
    wss
    @1
    @2
    @4
    @3
    cS
    cG
    subgrcl
    3ad2ant1
    @1
    @2
    @6
    @3
    @5
    cS
    cG
    @5
    eqid
    #
    subgss
    3ad2ant1
    @2
    @1
    @7
    @3
    @5
    cU
    cG
    @8
    subgss
    3ad2ant2
    @1
    @2
    @3
    simp3
    @5
    c.po
    cS
    cT
    cU
    cG
    cgrp
    @8
    lsmub1.p
    lsmless2x
    syl31anc
end
