include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "subgrcl.mm"
include "adantr.mm"
include "eqid.mm"
include "subgss.mm"
include "adantl.mm"
include "3jca.mm"
include "lsmelvalix.mm"
include "sylan.mm"

theorem lsmelvali
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume lsmelval.a: |- .+ = ( +g ` G )
  assume lsmelval.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) /\ ( X e. T /\ Y e. U ) ) -> ( X .+ Y ) e. ( T .(+) U ) )

  proof
    cT
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
    cG
    cgrp
    wcel
    #
    cT
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
    w3a
    cX
    cT
    wcel
    cY
    cU
    wcel
    wa
    cX
    cY
    c.pl
    co
    cT
    cU
    c.po
    co
    wcel
    @3
    @4
    @6
    @7
    @1
    @4
    @2
    cT
    cG
    subgrcl
    adantr
    @1
    @6
    @2
    @5
    cT
    cG
    @5
    eqid
    #
    subgss
    adantr
    @2
    @7
    @1
    @5
    cU
    cG
    @8
    subgss
    adantl
    3jca
    @5
    c.pl
    c.po
    cT
    cU
    cG
    cgrp
    cX
    cY
    @8
    lsmelval.a
    lsmelval.p
    lsmelvalix
    sylan
end
