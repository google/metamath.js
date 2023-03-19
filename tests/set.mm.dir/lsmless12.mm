include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "co.mm"
include "cgrp.mm"
include "cbs.mm"
include "subgrcl.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "subgss.mm"
include "simprr.mm"
include "ad2antlr.mm"
include "sstrd.mm"
include "simprl.mm"
include "lsmless1x.mm"
include "syl31anc.mm"
include "simpll.mm"
include "simplr.mm"
include "lsmless2.mm"
include "syl3anc.mm"

theorem lsmless12
  let c.po: class .(+)
  let cR: class R
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
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( ( S e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) /\ ( R C_ S /\ T C_ U ) ) -> ( R .(+) T ) C_ ( S .(+) U ) )

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
    wa
    #
    cR
    cS
    wss
    #
    cT
    cU
    wss
    #
    wa
    #
    wa
    #
    cR
    cT
    c.po
    co
    #
    cS
    cT
    c.po
    co
    #
    cS
    cU
    c.po
    co
    #
    @7
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
    cT
    @12
    wss
    @4
    @8
    @9
    wss
    @1
    @11
    @2
    @6
    cS
    cG
    subgrcl
    ad2antrr
    @1
    @13
    @2
    @6
    @12
    cS
    cG
    @12
    eqid
    #
    subgss
    ad2antrr
    @7
    cT
    cU
    @12
    @3
    @4
    @5
    simprr
    #
    @2
    cU
    @12
    wss
    @1
    @6
    @12
    cU
    cG
    @14
    subgss
    ad2antlr
    sstrd
    @3
    @4
    @5
    simprl
    @12
    c.po
    cR
    cS
    cT
    cG
    cgrp
    @14
    lsmub1.p
    lsmless1x
    syl31anc
    @7
    @1
    @2
    @5
    @9
    @10
    wss
    @1
    @2
    @6
    simpll
    @1
    @2
    @6
    simplr
    @15
    c.po
    cS
    cT
    cU
    cG
    lsmub1.p
    lsmless2
    syl3anc
    sstrd
end
