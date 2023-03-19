include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cgrp.mm"
include "wceq.mm"
include "ablgrp.mm"
include "grpinvadd.mm"
include "syl3an1.mm"
include "simp1.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "eqtr4d.mm"

theorem ablinvadd
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  assume ablinvadd.b: |- B = ( Base ` G )
  assume ablinvadd.p: |- .+ = ( +g ` G )
  assume ablinvadd.n: |- N = ( invg ` G )


  assert |- ( ( G e. Abel /\ X e. B /\ Y e. B ) -> ( N ` ( X .+ Y ) ) = ( ( N ` X ) .+ ( N ` Y ) ) )

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
    cN
    cfv
    #
    cY
    cN
    cfv
    #
    cX
    cN
    cfv
    #
    c.pl
    co
    #
    @6
    @5
    c.pl
    co
    #
    @0
    cG
    cgrp
    wcel
    #
    @1
    @2
    @4
    @7
    wceq
    cG
    ablgrp
    #
    cB
    c.pl
    cG
    cN
    cX
    cY
    ablinvadd.b
    ablinvadd.p
    ablinvadd.n
    grpinvadd
    syl3an1
    @3
    @0
    @6
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @8
    @7
    wceq
    @0
    @1
    @2
    simp1
    @3
    @9
    @1
    @11
    @0
    @1
    @9
    @2
    @10
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    cB
    cG
    cN
    cX
    ablinvadd.b
    ablinvadd.n
    grpinvcl
    syl2anc
    @3
    @9
    @2
    @12
    @13
    @0
    @1
    @2
    simp3
    cB
    cG
    cN
    cY
    ablinvadd.b
    ablinvadd.n
    grpinvcl
    syl2anc
    cB
    c.pl
    cG
    @6
    @5
    ablinvadd.b
    ablinvadd.p
    ablcom
    syl3anc
    eqtr4d
end
