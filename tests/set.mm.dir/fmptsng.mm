include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "copab.mm"
include "csn.mm"
include "cop.mm"
include "cmpt.mm"
include "velsn.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "eqidd.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "sylan9bbr.mm"
include "anbi12d.mm"
include "opelopabga.mm"
include "mpbir2and.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "wex.mm"
include "elopab.mm"
include "wi.mm"
include "opeq12.mm"
include "opeq2d.mm"
include "opex.mm"
include "snid.mm"
include "syl6eqel.mm"
include "sylbid.mm"
include "impcom.mm"
include "exlimivv.mm"
include "a1i.mm"
include "impbid.mm"
include "eqrdv.mm"
include "df-mpt.mm"
include "3eqtr4a.mm"

theorem fmptsng
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vy: setvar y
  assume fmptsng.1: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
  disjoint A p
  disjoint A y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint B p
  disjoint B y
  disjoint C p
  disjoint C y
  disjoint V p
  disjoint W p
  assert |- ( ( A e. V /\ C e. W ) -> { <. A , C >. } = ( x e. { A } |-> B ) )

  proof
    cA
    cV
    wcel
    cC
    cW
    wcel
    wa
    #
    vx
    cv
    #
    cA
    wceq
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    cA
    csn
    #
    wcel
    #
    @4
    wa
    #
    vx
    vy
    copab
    #
    cA
    cC
    cop
    #
    csn
    #
    vx
    @7
    cB
    cmpt
    #
    @5
    @9
    vx
    vy
    @2
    @8
    @4
    @8
    @2
    vx
    cA
    velsn
    bicomi
    anbi1i
    opabbii
    @0
    vp
    @12
    @6
    @0
    vp
    cv
    #
    @12
    wcel
    #
    @14
    @6
    wcel
    #
    @15
    @14
    @11
    wceq
    #
    @0
    @16
    vp
    @11
    velsn
    @0
    @16
    @17
    @11
    @6
    wcel
    #
    @0
    @18
    cA
    cA
    wceq
    #
    cC
    cC
    wceq
    #
    @0
    cA
    eqidd
    @0
    cC
    eqidd
    @5
    @19
    @20
    wa
    vx
    vy
    cA
    cC
    cV
    cW
    @2
    @3
    cC
    wceq
    #
    wa
    @2
    @19
    @4
    @20
    @2
    @2
    @19
    wb
    @21
    @1
    cA
    cA
    eqeq1
    adantr
    @21
    @4
    cC
    cB
    wceq
    @2
    @20
    @3
    cC
    cB
    eqeq1
    @2
    cB
    cC
    cC
    fmptsng.1
    eqeq2d
    sylan9bbr
    anbi12d
    opelopabga
    mpbir2and
    @14
    @11
    @6
    eleq1
    syl5ibrcom
    syl5bi
    @16
    @14
    @1
    @3
    cop
    #
    wceq
    #
    @5
    wa
    #
    vy
    wex
    vx
    wex
    #
    @0
    @15
    @5
    vx
    vy
    @14
    elopab
    @25
    @15
    wi
    @0
    @24
    @15
    vx
    vy
    @5
    @23
    @15
    @5
    @23
    @14
    cA
    cB
    cop
    #
    wceq
    #
    @15
    @5
    @22
    @26
    @14
    @1
    @3
    cA
    cB
    opeq12
    eqeq2d
    @5
    @15
    @27
    @26
    @12
    wcel
    @5
    @26
    @11
    @12
    @5
    cB
    cC
    cA
    @2
    cB
    cC
    wceq
    @4
    fmptsng.1
    adantr
    opeq2d
    @11
    cA
    cC
    opex
    snid
    syl6eqel
    @14
    @26
    @12
    eleq1
    syl5ibrcom
    sylbid
    impcom
    exlimivv
    a1i
    syl5bi
    impbid
    eqrdv
    @13
    @10
    wceq
    @0
    vx
    vy
    @7
    cB
    df-mpt
    a1i
    3eqtr4a
end
