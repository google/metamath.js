include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "posi.mm"
include "syl13anc.mm"
include "simp2d.mm"
include "posref.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "breq1.mm"
include "jcad.mm"
include "3adant3.mm"
include "impbid.mm"

theorem posasymb
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cZ: class Z
  assume posi.b: |- B = ( Base ` K )
  assume posi.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Poset /\ X e. B /\ Y e. B ) -> ( ( X .<_ Y /\ Y .<_ X ) <-> X = Y ) )

  proof
    cK
    cpo
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
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    wceq
    #
    @3
    cX
    cX
    c.le
    wbr
    #
    @6
    @7
    wi
    #
    @4
    cY
    cY
    c.le
    wbr
    wa
    @4
    wi
    #
    @3
    @0
    @1
    @2
    @2
    @8
    @9
    @10
    w3a
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @11
    cB
    cK
    c.le
    cX
    cY
    cY
    posi.b
    posi.l
    posi
    syl13anc
    simp2d
    @0
    @1
    @7
    @6
    wi
    @2
    @0
    @1
    wa
    #
    @7
    @4
    @5
    @12
    @8
    @7
    @4
    cB
    cK
    c.le
    cX
    posi.b
    posi.l
    posref
    #
    cX
    cY
    cX
    c.le
    breq2
    syl5ibcom
    @12
    @8
    @7
    @5
    @13
    cX
    cY
    cX
    c.le
    breq1
    syl5ibcom
    jcad
    3adant3
    impbid
end
