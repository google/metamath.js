include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "cpr.mm"
include "wral.mm"
include "wi.mm"
include "breq1.mm"
include "ralprg.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"

theorem joinval2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  assume joinval2.b: |- B = ( Base ` K )
  assume joinval2.l: |- .<_ = ( le ` K )
  assume joinval2.j: |- .\/ = ( join ` K )
  assume joinval2.k: |- ( ph -> K e. V )
  assume joinval2.x: |- ( ph -> X e. B )
  assume joinval2.y: |- ( ph -> Y e. B )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint .\/ x
  disjoint .\/ z
  disjoint x y
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint .<_ y
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( X e. B /\ Y e. B ) -> ( ( A. y e. { X , Y } y .<_ x /\ A. z e. B ( A. y e. { X , Y } y .<_ z -> x .<_ z ) ) <-> ( ( X .<_ x /\ Y .<_ x ) /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> x .<_ z ) ) ) )

  proof
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    vy
    cX
    cY
    cpr
    #
    wral
    cX
    @2
    c.le
    wbr
    #
    cY
    @2
    c.le
    wbr
    #
    wa
    @1
    vz
    cv
    #
    c.le
    wbr
    #
    vy
    @4
    wral
    #
    @2
    @7
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    cX
    @7
    c.le
    wbr
    #
    cY
    @7
    c.le
    wbr
    #
    wa
    #
    @10
    wi
    #
    vz
    cB
    wral
    @3
    @5
    @6
    vy
    cX
    cY
    cB
    cB
    @1
    cX
    @2
    c.le
    breq1
    @1
    cY
    @2
    c.le
    breq1
    ralprg
    @0
    @11
    @15
    vz
    cB
    @0
    @9
    @14
    @10
    @8
    @12
    @13
    vy
    cX
    cY
    cB
    cB
    @1
    cX
    @7
    c.le
    breq1
    @1
    cY
    @7
    c.le
    breq1
    ralprg
    imbi1d
    ralbidv
    anbi12d
end
