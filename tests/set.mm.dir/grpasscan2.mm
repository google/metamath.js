include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "simp3.mm"
include "grpass.mm"
include "syl13anc.mm"
include "eqid.mm"
include "grplinv.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3adant3.mm"
include "3eqtrd.mm"

theorem grpasscan2
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  assume grplcan.b: |- B = ( Base ` G )
  assume grplcan.p: |- .+ = ( +g ` G )
  assume grpasscan1.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( ( X .+ ( N ` Y ) ) .+ Y ) = X )

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
    w3a
    #
    cX
    cY
    cN
    cfv
    #
    c.pl
    co
    cY
    c.pl
    co
    #
    cX
    @4
    cY
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cG
    c0g
    cfv
    #
    c.pl
    co
    #
    cX
    @3
    @0
    @1
    @4
    cB
    wcel
    #
    @2
    @5
    @7
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @2
    @10
    @1
    cB
    cG
    cN
    cY
    grplcan.b
    grpasscan1.n
    grpinvcl
    3adant2
    @0
    @1
    @2
    simp3
    cB
    c.pl
    cG
    cX
    @4
    cY
    grplcan.b
    grplcan.p
    grpass
    syl13anc
    @3
    @6
    @8
    cX
    c.pl
    @0
    @2
    @6
    @8
    wceq
    @1
    cB
    c.pl
    cG
    cN
    cY
    @8
    grplcan.b
    grplcan.p
    @8
    eqid
    #
    grpasscan1.n
    grplinv
    3adant2
    oveq2d
    @0
    @1
    @9
    cX
    wceq
    @2
    cB
    c.pl
    cG
    cX
    @8
    grplcan.b
    grplcan.p
    @11
    grprid
    3adant3
    3eqtrd
end
