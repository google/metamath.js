include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "cpr.mm"
include "wral.mm"
include "wi.mm"
include "breq2.mm"
include "ralprg.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"

theorem meetval2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let cY: class Y
  assume meetval2.b: |- B = ( Base ` K )
  assume meetval2.l: |- .<_ = ( le ` K )
  assume meetval2.m: |- ./\ = ( meet ` K )
  assume meetval2.k: |- ( ph -> K e. V )
  assume meetval2.x: |- ( ph -> X e. B )
  assume meetval2.y: |- ( ph -> Y e. B )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint ./\ x
  disjoint ./\ z
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
  assert |- ( ( X e. B /\ Y e. B ) -> ( ( A. y e. { X , Y } x .<_ y /\ A. z e. B ( A. y e. { X , Y } z .<_ y -> z .<_ x ) ) <-> ( ( x .<_ X /\ x .<_ Y ) /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ x ) ) ) )

  proof
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    vx
    cv
    #
    vy
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
    @1
    cX
    c.le
    wbr
    #
    @1
    cY
    c.le
    wbr
    #
    wa
    vz
    cv
    #
    @2
    c.le
    wbr
    #
    vy
    @4
    wral
    #
    @7
    @1
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    @7
    cX
    c.le
    wbr
    #
    @7
    cY
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
    @2
    cX
    @1
    c.le
    breq2
    @2
    cY
    @1
    c.le
    breq2
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
    @2
    cX
    @7
    c.le
    breq2
    @2
    cY
    @7
    c.le
    breq2
    ralprg
    imbi1d
    ralbidv
    anbi12d
end
