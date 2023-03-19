include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cgrp.mm"
include "wss.mm"
include "co.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "wceq.mm"
include "subgrcl.mm"
include "adantr.mm"
include "subgss.mm"
include "adantl.mm"
include "lsmvalx.mm"
include "syl3anc.mm"

theorem lsmval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  assume lsmval.v: |- B = ( Base ` G )
  assume lsmval.a: |- .+ = ( +g ` G )
  assume lsmval.p: |- .(+) = ( LSSum ` G )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( T .(+) U ) = ran ( x e. T , y e. U |-> ( x .+ y ) ) )

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
    cB
    wss
    #
    cU
    cB
    wss
    #
    cT
    cU
    c.po
    co
    vx
    vy
    cT
    cU
    vx
    cv
    vy
    cv
    c.pl
    co
    cmpt2
    crn
    wceq
    @1
    @3
    @2
    cT
    cG
    subgrcl
    adantr
    @1
    @4
    @2
    cB
    cT
    cG
    lsmval.v
    subgss
    adantr
    @2
    @5
    @1
    cB
    cU
    cG
    lsmval.v
    subgss
    adantl
    vx
    vy
    cB
    c.pl
    c.po
    cT
    cU
    cG
    cgrp
    lsmval.v
    lsmval.a
    lsmval.p
    lsmvalx
    syl3anc
end
