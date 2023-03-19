include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "co.mm"
include "wceq.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "0subg.mm"
include "syl.mm"
include "subg0cl.mm"
include "snssd.mm"
include "lsmss2.mm"
include "mpd3an23.mm"

theorem lsm01
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let c.0: class .0.
  assume lsm01.z: |- .0. = ( 0g ` G )
  assume lsm01.p: |- .(+) = ( LSSum ` G )


  assert |- ( X e. ( SubGrp ` G ) -> ( X .(+) { .0. } ) = X )

  proof
    cX
    cG
    csubg
    cfv
    #
    wcel
    #
    c.0
    csn
    #
    @0
    wcel
    #
    @2
    cX
    wss
    cX
    @2
    c.po
    co
    cX
    wceq
    @1
    cG
    cgrp
    wcel
    @3
    cX
    cG
    subgrcl
    cG
    c.0
    lsm01.z
    0subg
    syl
    @1
    c.0
    cX
    cX
    cG
    c.0
    lsm01.z
    subg0cl
    snssd
    c.po
    cX
    @2
    cG
    lsm01.p
    lsmss2
    mpd3an23
end
