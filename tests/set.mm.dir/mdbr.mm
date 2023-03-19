include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cmd.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "ineq1d.mm"
include "ineq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "sseq2.mm"
include "ineq2.mm"
include "imbi12d.mm"
include "df-md.mm"
include "brabg.mm"
include "bianabs.mm"

theorem mdbr
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
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH B <-> A. x e. CH ( x C_ B -> ( ( x vH A ) i^i B ) = ( x vH ( A i^i B ) ) ) ) )

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
    cmd
    wbr
    vx
    cv
    #
    cB
    wss
    #
    @3
    cA
    chj
    co
    #
    cB
    cin
    #
    @3
    cA
    cB
    cin
    #
    chj
    co
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
    @3
    @14
    wss
    #
    @3
    @12
    chj
    co
    #
    @14
    cin
    #
    @3
    @12
    @14
    cin
    #
    chj
    co
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
    cin
    #
    @3
    cA
    @14
    cin
    #
    chj
    co
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
    cmd
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
    @12
    cA
    @3
    chj
    oveq2
    ineq1d
    @32
    @20
    @27
    @3
    chj
    @12
    cA
    @14
    ineq1
    oveq2d
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
    sseq2
    @33
    @26
    @6
    @28
    @8
    @14
    cB
    @5
    ineq2
    @33
    @27
    @7
    @3
    chj
    @14
    cB
    cA
    ineq2
    oveq2d
    eqeq12d
    imbi12d
    ralbidv
    anbi12d
    vy
    vz
    vx
    df-md
    brabg
    bianabs
end
