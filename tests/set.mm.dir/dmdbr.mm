include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "ineq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "ineq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "sseq1.mm"
include "oveq2.mm"
include "imbi12d.mm"
include "df-dmd.mm"
include "brabg.mm"
include "bianabs.mm"

theorem dmdbr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH* B <-> A. x e. CH ( B C_ x -> ( ( x i^i A ) vH B ) = ( x i^i ( A vH B ) ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cB
    cdmd
    wbr
    cB
    vx
    cv
    #
    wss
    #
    @3
    cA
    cin
    #
    cB
    chj
    co
    #
    @3
    cA
    cB
    chj
    co
    #
    cin
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    #
    vy
    cv
    #
    cch
    wcel
    #
    vz
    cv
    #
    cch
    wcel
    #
    wa
    #
    @14
    @3
    wss
    #
    @3
    @12
    cin
    #
    @14
    chj
    co
    #
    @3
    @12
    @14
    chj
    co
    #
    cin
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    #
    wa
    @0
    @15
    wa
    #
    @17
    @5
    @14
    chj
    co
    #
    @3
    cA
    @14
    chj
    co
    #
    cin
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    #
    wa
    @2
    @11
    wa
    vy
    vz
    cA
    cB
    cch
    cch
    cdmd
    @12
    cA
    wceq
    #
    @16
    @25
    @24
    @31
    @32
    @13
    @0
    @15
    @12
    cA
    cch
    eleq1
    anbi1d
    @32
    @23
    @30
    vx
    cch
    @32
    @22
    @29
    @17
    @32
    @19
    @26
    @21
    @28
    @32
    @18
    @5
    @14
    chj
    @12
    cA
    @3
    ineq2
    oveq1d
    @32
    @20
    @27
    @3
    @12
    cA
    @14
    chj
    oveq1
    ineq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    @14
    cB
    wceq
    #
    @25
    @2
    @31
    @11
    @33
    @15
    @1
    @0
    @14
    cB
    cch
    eleq1
    anbi2d
    @33
    @30
    @10
    vx
    cch
    @33
    @17
    @4
    @29
    @9
    @14
    cB
    @3
    sseq1
    @33
    @26
    @6
    @28
    @8
    @14
    cB
    @5
    chj
    oveq2
    @33
    @27
    @7
    @3
    @14
    cB
    cA
    chj
    oveq2
    ineq2d
    eqeq12d
    imbi12d
    ralbidv
    anbi12d
    vy
    vz
    vx
    df-dmd
    brabg
    bianabs
end
