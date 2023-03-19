include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cgrp.mm"
include "wceq.mm"
include "csubg.mm"
include "nsgsubg.mm"
include "3ad2ant1.mm"
include "subgrcl.mm"
include "syl.mm"
include "simp2.mm"
include "wss.mm"
include "subgss.mm"
include "simp3.mm"
include "sseldd.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "grpnpcan.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "wb.mm"
include "simp1.mm"
include "grpsubcl.mm"
include "nsgbi.mm"
include "mpbid.mm"

theorem nsgconj
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isnsg3.1: |- X = ( Base ` G )
  assume isnsg3.2: |- .+ = ( +g ` G )
  assume isnsg3.3: |- .- = ( -g ` G )


  assert |- ( ( S e. ( NrmSGrp ` G ) /\ A e. X /\ B e. S ) -> ( ( A .+ B ) .- A ) e. S )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    #
    cA
    cB
    c.pl
    co
    cA
    c.mi
    co
    #
    cA
    cB
    cA
    c.mi
    co
    #
    c.pl
    co
    #
    cS
    @3
    cG
    cgrp
    wcel
    #
    @1
    cB
    cX
    wcel
    #
    @1
    @4
    @6
    wceq
    @3
    cS
    cG
    csubg
    cfv
    wcel
    #
    @7
    @0
    @1
    @9
    @2
    cS
    cG
    nsgsubg
    3ad2ant1
    #
    cS
    cG
    subgrcl
    syl
    #
    @0
    @1
    @2
    simp2
    #
    @3
    cS
    cX
    cB
    @3
    @9
    cS
    cX
    wss
    @10
    cX
    cS
    cG
    isnsg3.1
    subgss
    syl
    @0
    @1
    @2
    simp3
    #
    sseldd
    #
    @12
    cX
    c.pl
    cG
    c.mi
    cA
    cB
    cA
    isnsg3.1
    isnsg3.2
    isnsg3.3
    grpaddsubass
    syl13anc
    @3
    @5
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    @6
    cS
    wcel
    #
    @3
    @15
    cB
    cS
    @3
    @7
    @8
    @1
    @15
    cB
    wceq
    @11
    @14
    @12
    cX
    c.pl
    cG
    c.mi
    cB
    cA
    isnsg3.1
    isnsg3.2
    isnsg3.3
    grpnpcan
    syl3anc
    @13
    eqeltrd
    @3
    @0
    @5
    cX
    wcel
    #
    @1
    @16
    @17
    wb
    @0
    @1
    @2
    simp1
    @3
    @7
    @8
    @1
    @18
    @11
    @14
    @12
    cX
    cG
    c.mi
    cB
    cA
    isnsg3.1
    isnsg3.3
    grpsubcl
    syl3anc
    @12
    @5
    cA
    c.pl
    cS
    cG
    cX
    isnsg3.1
    isnsg3.2
    nsgbi
    syl3anc
    mpbid
    eqeltrd
end
