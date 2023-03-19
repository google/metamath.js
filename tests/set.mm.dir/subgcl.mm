include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cress.mm"
include "co.mm"
include "cplusg.mm"
include "cbs.mm"
include "cgrp.mm"
include "eqid.mm"
include "subggrp.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "subgbas.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "3eltr4d.mm"

theorem subgcl
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cX: class X
  let cY: class Y
  assume subgcl.p: |- .+ = ( +g ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ X e. S /\ Y e. S ) -> ( X .+ Y ) e. S )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    w3a
    #
    cX
    cY
    cG
    cS
    cress
    co
    #
    cplusg
    cfv
    #
    co
    #
    @5
    cbs
    cfv
    #
    cX
    cY
    c.pl
    co
    cS
    @4
    @5
    cgrp
    wcel
    #
    cX
    @8
    wcel
    cY
    @8
    wcel
    @7
    @8
    wcel
    @1
    @2
    @9
    @3
    cS
    cG
    @5
    @5
    eqid
    #
    subggrp
    3ad2ant1
    @4
    cX
    cS
    @8
    @1
    @2
    @3
    simp2
    @1
    @2
    cS
    @8
    wceq
    @3
    cS
    cG
    @5
    @10
    subgbas
    3ad2ant1
    #
    eleqtrd
    @4
    cY
    cS
    @8
    @1
    @2
    @3
    simp3
    @11
    eleqtrd
    @8
    @6
    @5
    cX
    cY
    @8
    eqid
    @6
    eqid
    grpcl
    syl3anc
    @4
    c.pl
    @6
    cX
    cY
    @1
    @2
    c.pl
    @6
    wceq
    @3
    cS
    c.pl
    cG
    @5
    @0
    @10
    subgcl.p
    ressplusg
    3ad2ant1
    oveqd
    @11
    3eltr4d
end
