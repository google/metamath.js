include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "subgrcl.mm"
include "adantr.mm"
include "eqid.mm"
include "subgss.mm"
include "adantl.mm"
include "lsmelvalx.mm"
include "syl3anc.mm"

theorem lsmelval
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cX: class X
  assume lsmelval.a: |- .+ = ( +g ` G )
  assume lsmelval.p: |- .(+) = ( LSSum ` G )

  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint T y
  disjoint T z
  disjoint U y
  disjoint U z
  disjoint G y
  disjoint G z
  disjoint X y
  disjoint X z
  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( X e. ( T .(+) U ) <-> E. y e. T E. z e. U X = ( y .+ z ) ) )

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
    @4
    wss
    #
    cX
    cT
    cU
    c.po
    co
    wcel
    cX
    vy
    cv
    vz
    cv
    c.pl
    co
    wceq
    vz
    cU
    wrex
    vy
    cT
    wrex
    wb
    @1
    @3
    @2
    cT
    cG
    subgrcl
    adantr
    @1
    @5
    @2
    @4
    cT
    cG
    @4
    eqid
    #
    subgss
    adantr
    @2
    @6
    @1
    @4
    cU
    cG
    @7
    subgss
    adantl
    vy
    vz
    @4
    c.pl
    c.po
    cT
    cU
    cG
    cgrp
    cX
    @7
    lsmelval.a
    lsmelval.p
    lsmelvalx
    syl3anc
end
