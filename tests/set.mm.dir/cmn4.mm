include "ccmn.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cmnd.mm"
include "simp1.mm"
include "cmnmnd.mm"
include "syl.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "co.mm"
include "wceq.mm"
include "cmncom.mm"
include "syl3anc.mm"
include "mnd4g.mm"

theorem cmn4
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume ablcom.b: |- B = ( Base ` G )
  assume ablcom.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. CMnd /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .+ Y ) .+ ( Z .+ W ) ) = ( ( X .+ Z ) .+ ( Y .+ W ) ) )

  proof
    cG
    ccmn
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
    wa
    #
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    w3a
    #
    cB
    c.pl
    cG
    cW
    cX
    cY
    cZ
    ablcom.b
    ablcom.p
    @7
    @0
    cG
    cmnd
    wcel
    @0
    @3
    @6
    simp1
    #
    cG
    cmnmnd
    syl
    @0
    @1
    @2
    @6
    simp2l
    @0
    @1
    @2
    @6
    simp2r
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    @7
    @0
    @2
    @4
    cY
    cZ
    c.pl
    co
    cZ
    cY
    c.pl
    co
    wceq
    @8
    @9
    @10
    cB
    c.pl
    cG
    cY
    cZ
    ablcom.b
    ablcom.p
    cmncom
    syl3anc
    mnd4g
end
