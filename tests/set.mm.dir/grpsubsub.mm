include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr1.mm"
include "grpsubcl.mm"
include "3adant3r1.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "grpinvsub.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpsubsub
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume grpsubadd.b: |- B = ( Base ` G )
  assume grpsubadd.p: |- .+ = ( +g ` G )
  assume grpsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .- ( Y .- Z ) ) = ( X .+ ( Z .- Y ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    wa
    #
    cX
    cY
    cZ
    c.mi
    co
    #
    c.mi
    co
    #
    cX
    @5
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cX
    cZ
    cY
    c.mi
    co
    #
    c.pl
    co
    @4
    @1
    @5
    cB
    wcel
    #
    @6
    @9
    wceq
    @0
    @1
    @2
    @3
    simpr1
    @0
    @2
    @3
    @11
    @1
    cB
    cG
    c.mi
    cY
    cZ
    grpsubadd.b
    grpsubadd.m
    grpsubcl
    3adant3r1
    cB
    c.pl
    cG
    @7
    c.mi
    cX
    @5
    grpsubadd.b
    grpsubadd.p
    @7
    eqid
    #
    grpsubadd.m
    grpsubval
    syl2anc
    @4
    @8
    @10
    cX
    c.pl
    @0
    @2
    @3
    @8
    @10
    wceq
    @1
    cB
    cG
    c.mi
    @7
    cY
    cZ
    grpsubadd.b
    grpsubadd.m
    @12
    grpinvsub
    3adant3r1
    oveq2d
    eqtrd
end
