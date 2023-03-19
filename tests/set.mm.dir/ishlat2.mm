include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cal.mm"
include "wn.mm"
include "ishlat1.mm"
include "iscvlat.mm"
include "3anbi3i.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "bitri.mm"
include "ancom.mm"
include "r19.26-2.mm"
include "bitr4i.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "3bitri.mm"

theorem ishlat2
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
  let vk: setvar k
  assume ishlat.b: |- B = ( Base ` K )
  assume ishlat.l: |- .<_ = ( le ` K )
  assume ishlat.s: |- .< = ( lt ` K )
  assume ishlat.j: |- .\/ = ( join ` K )
  assume ishlat.z: |- .0. = ( 0. ` K )
  assume ishlat.u: |- .1. = ( 1. ` K )
  assume ishlat.a: |- A = ( Atoms ` K )

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
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint B k
  disjoint .\/ k
  disjoint K k
  disjoint .<_ k
  disjoint .< k
  disjoint .1. k
  disjoint .0. k
  assert |- ( K e. HL <-> ( ( K e. OML /\ K e. CLat /\ K e. AtLat ) /\ ( A. x e. A A. y e. A ( ( x =/= y -> E. z e. A ( z =/= x /\ z =/= y /\ z .<_ ( x .\/ y ) ) ) /\ A. z e. B ( ( -. x .<_ z /\ x .<_ ( z .\/ y ) ) -> y .<_ ( z .\/ x ) ) ) /\ E. x e. B E. y e. B E. z e. B ( ( .0. .< x /\ x .< y ) /\ ( y .< z /\ z .< .1. ) ) ) ) )

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
    clc
    wcel
    #
    w3a
    #
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
    @4
    wne
    @6
    @5
    wne
    @6
    @4
    @5
    c.or
    co
    c.le
    wbr
    w3a
    vz
    cA
    wrex
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    c.0
    @4
    c.lt
    wbr
    @4
    @5
    c.lt
    wbr
    wa
    @5
    @6
    c.lt
    wbr
    @6
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
    #
    wa
    @0
    @1
    cK
    cal
    wcel
    #
    w3a
    #
    @4
    @6
    c.le
    wbr
    wn
    @4
    @6
    @5
    c.or
    co
    c.le
    wbr
    wa
    @5
    @6
    @4
    c.or
    co
    c.le
    wbr
    wi
    vz
    cB
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    #
    @10
    wa
    #
    @12
    @7
    @13
    wa
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @9
    wa
    #
    wa
    #
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
    ishlat.b
    ishlat.l
    ishlat.s
    ishlat.j
    ishlat.z
    ishlat.u
    ishlat.a
    ishlat1
    @3
    @15
    @10
    @3
    @0
    @1
    @11
    @14
    wa
    #
    w3a
    #
    @15
    @2
    @20
    @0
    @1
    vz
    cA
    cB
    c.or
    cK
    c.le
    vy
    vx
    ishlat.b
    ishlat.l
    ishlat.j
    ishlat.a
    iscvlat
    3anbi3i
    @0
    @1
    wa
    #
    @11
    wa
    #
    @14
    wa
    @22
    @20
    wa
    @15
    @21
    @22
    @11
    @14
    anass
    @12
    @23
    @14
    @0
    @1
    @11
    df-3an
    anbi1i
    @0
    @1
    @20
    df-3an
    3bitr4ri
    bitri
    anbi1i
    @16
    @12
    @14
    @10
    wa
    #
    wa
    @19
    @12
    @14
    @10
    anass
    @24
    @18
    @12
    @24
    @14
    @8
    wa
    #
    @9
    wa
    @18
    @14
    @8
    @9
    anass
    @25
    @17
    @9
    @25
    @8
    @14
    wa
    @17
    @14
    @8
    ancom
    @7
    @13
    vx
    vy
    cA
    cA
    r19.26-2
    bitr4i
    anbi1i
    bitr3i
    anbi2i
    bitri
    3bitri
end
