include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "abladdsub.mm"
include "syl13anc.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "grplid.mm"
include "3eqtrd.mm"

theorem ablpncan2
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume ablsubadd.b: |- B = ( Base ` G )
  assume ablsubadd.p: |- .+ = ( +g ` G )
  assume ablsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Abel /\ X e. B /\ Y e. B ) -> ( ( X .+ Y ) .- X ) = Y )

  proof
    cG
    cabl
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
    c.pl
    co
    cX
    c.mi
    co
    #
    cX
    cX
    c.mi
    co
    #
    cY
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    cY
    c.pl
    co
    #
    cY
    @3
    @0
    @1
    @2
    @1
    @4
    @6
    wceq
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    @10
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    cX
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    abladdsub
    syl13anc
    @3
    @5
    @7
    cY
    c.pl
    @3
    cG
    cgrp
    wcel
    #
    @1
    @5
    @7
    wceq
    @3
    @0
    @12
    @9
    cG
    ablgrp
    syl
    #
    @10
    cB
    cG
    c.mi
    cX
    @7
    ablsubadd.b
    @7
    eqid
    #
    ablsubadd.m
    grpsubid
    syl2anc
    oveq1d
    @3
    @12
    @2
    @8
    cY
    wceq
    @13
    @11
    cB
    c.pl
    cG
    cY
    @7
    ablsubadd.b
    ablsubadd.p
    @14
    grplid
    syl2anc
    3eqtrd
end
