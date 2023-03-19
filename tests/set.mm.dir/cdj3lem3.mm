include "wcel.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cva.mm"
include "co.mm"
include "cfv.mm"
include "incom.mm"
include "eqeq1i.mm"
include "w3a.mm"
include "wa.mm"
include "chil.mm"
include "sheli.mm"
include "ax-hvcom.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "3adant3.mm"
include "cph.mm"
include "cv.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "shscomi.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "riotabiia.mm"
include "mpteq12i.mm"
include "eqtr4i.mm"
include "cdj3lem2.mm"
include "eqtr3d.mm"
include "syl3an3b.mm"
include "3com12.mm"

theorem cdj3lem3
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vu: setvar u
  let vv: setvar v
  let vt: setvar t
  let vh: setvar h
  let vy: setvar y
  assume cdj3lem2.1: |- A e. SH
  assume cdj3lem2.2: |- B e. SH
  assume cdj3lem3.3: |- T = ( x e. ( A +H B ) |-> ( iota_ w e. B E. z e. A x = ( z +h w ) ) )

  disjoint x z
  disjoint w x
  disjoint A x
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B z
  disjoint B w
  disjoint C x
  disjoint C z
  disjoint C w
  disjoint D x
  disjoint D z
  disjoint D w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint T v
  disjoint t u
  disjoint h u
  disjoint T u
  disjoint h t
  disjoint T t
  disjoint T h
  disjoint x y
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint A y
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint A v
  disjoint t u
  disjoint h u
  disjoint A u
  disjoint h t
  disjoint A t
  disjoint A h
  disjoint B y
  disjoint B v
  disjoint B u
  disjoint B t
  disjoint B h
  disjoint C y
  disjoint C v
  disjoint C u
  disjoint D y
  assert |- ( ( C e. A /\ D e. B /\ ( A i^i B ) = 0H ) -> ( T ` ( C +h D ) ) = D )

  proof
    cD
    cB
    wcel
    #
    cC
    cA
    wcel
    #
    cA
    cB
    cin
    #
    c0h
    wceq
    #
    cC
    cD
    cva
    co
    #
    cT
    cfv
    #
    cD
    wceq
    #
    @3
    @0
    @1
    cB
    cA
    cin
    #
    c0h
    wceq
    #
    @6
    @2
    @7
    c0h
    cA
    cB
    incom
    eqeq1i
    @0
    @1
    @8
    w3a
    cD
    cC
    cva
    co
    #
    cT
    cfv
    #
    @5
    cD
    @0
    @1
    @10
    @5
    wceq
    @8
    @0
    @1
    wa
    @9
    @4
    cT
    @0
    cD
    chil
    wcel
    cC
    chil
    wcel
    @9
    @4
    wceq
    @1
    cD
    cB
    cdj3lem2.2
    sheli
    cC
    cA
    cdj3lem2.1
    sheli
    cD
    cC
    ax-hvcom
    syl2an
    fveq2d
    3adant3
    vx
    vw
    vz
    cB
    cA
    cD
    cC
    cT
    cdj3lem2.2
    cdj3lem2.1
    cT
    vx
    cA
    cB
    cph
    co
    #
    vx
    cv
    #
    vz
    cv
    #
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vw
    cB
    crio
    #
    cmpt
    vx
    cB
    cA
    cph
    co
    #
    @12
    @14
    @13
    cva
    co
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vw
    cB
    crio
    #
    cmpt
    cdj3lem3.3
    vx
    @19
    @23
    @11
    @18
    cB
    cA
    cdj3lem2.2
    cdj3lem2.1
    shscomi
    @22
    @17
    vw
    cB
    @14
    cB
    wcel
    #
    @21
    @16
    vz
    cA
    @24
    @13
    cA
    wcel
    #
    wa
    @20
    @15
    @12
    @24
    @14
    chil
    wcel
    @13
    chil
    wcel
    @20
    @15
    wceq
    @25
    @14
    cB
    cdj3lem2.2
    sheli
    @13
    cA
    cdj3lem2.1
    sheli
    @14
    @13
    ax-hvcom
    syl2an
    eqeq2d
    rexbidva
    riotabiia
    mpteq12i
    eqtr4i
    cdj3lem2
    eqtr3d
    syl3an3b
    3com12
end
