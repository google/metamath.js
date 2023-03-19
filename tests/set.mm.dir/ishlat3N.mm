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
include "wceq.mm"
include "ishlat1.mm"
include "wb.mm"
include "simpll3.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "cvlsupr3.mm"
include "syl13anc.mm"
include "rexbidva.mm"
include "c0.mm"
include "ne0i.mm"
include "ad2antrl.mm"
include "r19.37zv.mm"
include "syl.mm"
include "bitr2d.mm"
include "2ralbidva.mm"
include "anbi1d.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem ishlat3N
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
  assert |- ( K e. HL <-> ( ( K e. OML /\ K e. CLat /\ K e. CvLat ) /\ ( A. x e. A A. y e. A E. z e. A ( x .\/ z ) = ( y .\/ z ) /\ E. x e. B E. y e. B E. z e. B ( ( .0. .< x /\ x .< y ) /\ ( y .< z /\ z .< .1. ) ) ) ) )

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
    #
    vz
    cv
    #
    @4
    wne
    @7
    @5
    wne
    @7
    @4
    @5
    c.or
    co
    c.le
    wbr
    w3a
    #
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
    @7
    c.lt
    wbr
    @7
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
    @3
    @4
    @7
    c.or
    co
    @5
    @7
    c.or
    co
    wceq
    #
    vz
    cA
    wrex
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @11
    wa
    #
    wa
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
    @12
    @16
    @3
    @10
    @15
    @11
    @3
    @9
    @14
    vx
    vy
    cA
    cA
    @3
    @4
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    wa
    #
    @14
    @6
    @8
    wi
    #
    vz
    cA
    wrex
    #
    @9
    @20
    @13
    @21
    vz
    cA
    @20
    @7
    cA
    wcel
    #
    wa
    @2
    @17
    @18
    @23
    @13
    @21
    wb
    @0
    @1
    @2
    @19
    @23
    simpll3
    @3
    @17
    @18
    @23
    simplrl
    @3
    @17
    @18
    @23
    simplrr
    @20
    @23
    simpr
    cA
    @4
    @5
    @7
    c.or
    cK
    c.le
    ishlat.a
    ishlat.l
    ishlat.j
    cvlsupr3
    syl13anc
    rexbidva
    @20
    cA
    c0
    wne
    #
    @22
    @9
    wb
    @17
    @24
    @3
    @18
    cA
    @4
    ne0i
    ad2antrl
    @6
    @8
    vz
    cA
    r19.37zv
    syl
    bitr2d
    2ralbidva
    anbi1d
    pm5.32i
    bitri
end
