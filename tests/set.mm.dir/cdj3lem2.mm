include "wcel.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wrex.mm"
include "crio.mm"
include "wa.mm"
include "cph.mm"
include "shsvai.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "syl.mm"
include "3adant3.mm"
include "eqid.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "3ad2ant2.mm"
include "wreu.mm"
include "wb.mm"
include "simp1.mm"
include "cdjreui.mm"
include "stoic3.mm"
include "oveq1.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem cdj3lem2
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vu: setvar u
  let vv: setvar v
  let vt: setvar t
  let vh: setvar h
  let vy: setvar y
  assume cdj3lem2.1: |- A e. SH
  assume cdj3lem2.2: |- B e. SH
  assume cdj3lem2.3: |- S = ( x e. ( A +H B ) |-> ( iota_ z e. A E. w e. B x = ( z +h w ) ) )

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
  disjoint S v
  disjoint t u
  disjoint h u
  disjoint S u
  disjoint h t
  disjoint S t
  disjoint S h
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
  assert |- ( ( C e. A /\ D e. B /\ ( A i^i B ) = 0H ) -> ( S ` ( C +h D ) ) = C )

  proof
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    cA
    cB
    cin
    c0h
    wceq
    #
    w3a
    #
    cC
    cD
    cva
    co
    #
    cS
    cfv
    #
    @4
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
    vw
    cB
    wrex
    #
    vz
    cA
    crio
    #
    cC
    @0
    @1
    @5
    @11
    wceq
    #
    @2
    @0
    @1
    wa
    @4
    cA
    cB
    cph
    co
    #
    wcel
    #
    @12
    cA
    cB
    cC
    cD
    cdj3lem2.1
    cdj3lem2.2
    shsvai
    #
    vx
    @4
    vx
    cv
    #
    @8
    wceq
    #
    vw
    cB
    wrex
    #
    vz
    cA
    crio
    @11
    @13
    cS
    @16
    @4
    wceq
    #
    @18
    @10
    vz
    cA
    @19
    @17
    @9
    vw
    cB
    @16
    @4
    @8
    eqeq1
    rexbidv
    riotabidv
    cdj3lem2.3
    @10
    vz
    cA
    riotaex
    fvmpt
    syl
    3adant3
    @3
    @4
    cC
    @7
    cva
    co
    #
    wceq
    #
    vw
    cB
    wrex
    #
    @11
    cC
    wceq
    #
    @1
    @0
    @22
    @2
    @1
    @4
    @4
    wceq
    #
    @22
    @4
    eqid
    @21
    @24
    vw
    cD
    cB
    @7
    cD
    wceq
    @20
    @4
    @4
    @7
    cD
    cC
    cva
    oveq2
    eqeq2d
    rspcev
    mpan2
    3ad2ant2
    @3
    @0
    @10
    vz
    cA
    wreu
    #
    @22
    @23
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @14
    @2
    @25
    @15
    vz
    vw
    cA
    cB
    @4
    cdj3lem2.1
    cdj3lem2.2
    cdjreui
    stoic3
    @10
    @22
    vz
    cA
    cC
    @6
    cC
    wceq
    #
    @9
    @21
    vw
    cB
    @26
    @8
    @20
    @4
    @6
    cC
    @7
    cva
    oveq1
    eqeq2d
    rexbidv
    riota2
    syl2anc
    mpbid
    eqtrd
end
