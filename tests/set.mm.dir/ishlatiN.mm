include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wral.mm"
include "3pm3.2i.mm"
include "pm3.2i.mm"
include "ishlat2.mm"
include "mpbir2an.mm"

theorem ishlatiN
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.0: class .0.
  assume ishlati.1: |- K e. OML
  assume ishlati.2: |- K e. CLat
  assume ishlati.3: |- K e. AtLat
  assume ishlati.b: |- B = ( Base ` K )
  assume ishlati.l: |- .<_ = ( le ` K )
  assume ishlati.s: |- .< = ( lt ` K )
  assume ishlati.j: |- .\/ = ( join ` K )
  assume ishlati.z: |- .0. = ( 0. ` K )
  assume ishlati.u: |- .1. = ( 1. ` K )
  assume ishlati.a: |- A = ( Atoms ` K )
  assume ishlati.9: |- A. x e. A A. y e. A ( ( x =/= y -> E. z e. A ( z =/= x /\ z =/= y /\ z .<_ ( x .\/ y ) ) ) /\ A. z e. B ( ( -. x .<_ z /\ x .<_ ( z .\/ y ) ) -> y .<_ ( z .\/ x ) ) )
  assume ishlati.10: |- E. x e. B E. y e. B E. z e. B ( ( .0. .< x /\ x .< y ) /\ ( y .< z /\ z .< .1. ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint K x
  disjoint K y
  disjoint K z
  assert |- K e. HL

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    cal
    wcel
    #
    w3a
    vx
    cv
    #
    vy
    cv
    #
    wne
    vz
    cv
    #
    @3
    wne
    @5
    @4
    wne
    @5
    @3
    @4
    c.or
    co
    c.le
    wbr
    w3a
    vz
    cA
    wrex
    wi
    @3
    @5
    c.le
    wbr
    wn
    @3
    @5
    @4
    c.or
    co
    c.le
    wbr
    wa
    @4
    @5
    @3
    c.or
    co
    c.le
    wbr
    wi
    vz
    cB
    wral
    wa
    vy
    cA
    wral
    vx
    cA
    wral
    #
    c.0
    @3
    c.lt
    wbr
    @3
    @4
    c.lt
    wbr
    wa
    @4
    @5
    c.lt
    wbr
    @5
    c.1
    c.lt
    wbr
    wa
    wa
    vz
    cB
    wrex
    vy
    cB
    wrex
    vx
    cB
    wrex
    #
    wa
    @0
    @1
    @2
    ishlati.1
    ishlati.2
    ishlati.3
    3pm3.2i
    @6
    @7
    ishlati.9
    ishlati.10
    pm3.2i
    vx
    vy
    vz
    cA
    cB
    c.lt
    c.1
    c.or
    cK
    c.le
    c.0
    ishlati.b
    ishlati.l
    ishlati.s
    ishlati.j
    ishlati.z
    ishlati.u
    ishlati.a
    ishlat2
    mpbir2an
end
