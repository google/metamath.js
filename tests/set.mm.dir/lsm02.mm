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
include "id.mm"
include "subg0cl.mm"
include "snssd.mm"
include "lsmss1.mm"
include "syl3anc.mm"

theorem lsm02
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let c.0: class .0.
  assume lsm01.z: |- .0. = ( 0g ` G )
  assume lsm01.p: |- .(+) = ( LSSum ` G )


  assert |- ( X e. ( SubGrp ` G ) -> ( { .0. } .(+) X ) = X )

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
    @1
    @2
    cX
    wss
    @2
    cX
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
    id
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
    @2
    cX
    cG
    lsm01.p
    lsmss1
    syl3anc
end
