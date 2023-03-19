include "cch.mm"
include "wcel.mm"
include "cv.mm"
include "cmd.mm"
include "wbr.mm"
include "wral.mm"
include "wss.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cdmd.mm"
include "breq2.mm"
include "cbvralv.mm"
include "wa.mm"
include "mdbr.mm"
include "incom.mm"
include "chjcom.mm"
include "ineq1d.mm"
include "syl5reqr.mm"
include "adantlr.mm"
include "oveq1i.mm"
include "chincl.mm"
include "sylan.mm"
include "eqeq12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "ralcom.mm"
include "dmdbr.mm"
include "bitr4d.mm"

theorem mddmd2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  assert |- ( A e. CH -> ( A. x e. CH A MH x <-> A. x e. CH A MH* x ) )

  proof
    cA
    cch
    wcel
    #
    cA
    vx
    cv
    #
    cmd
    wbr
    #
    vx
    cch
    wral
    #
    @1
    vy
    cv
    #
    wss
    #
    @4
    cA
    cin
    #
    @1
    chj
    co
    #
    @4
    cA
    @1
    chj
    co
    #
    cin
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    #
    vx
    cch
    wral
    #
    cA
    @1
    cdmd
    wbr
    #
    vx
    cch
    wral
    @0
    @3
    @11
    vx
    cch
    wral
    #
    vy
    cch
    wral
    #
    @13
    @3
    cA
    @4
    cmd
    wbr
    #
    vy
    cch
    wral
    @0
    @16
    @2
    @17
    vx
    vy
    cch
    @1
    @4
    cA
    cmd
    breq2
    cbvralv
    @0
    @17
    @15
    vy
    cch
    @0
    @4
    cch
    wcel
    #
    wa
    #
    @17
    @5
    @1
    cA
    chj
    co
    #
    @4
    cin
    #
    @1
    cA
    @4
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
    @15
    vx
    cA
    @4
    mdbr
    @19
    @25
    @11
    vx
    cch
    @19
    @1
    cch
    wcel
    #
    wa
    #
    @24
    @10
    @5
    @27
    @24
    @9
    @7
    wceq
    @10
    @27
    @21
    @9
    @23
    @7
    @0
    @26
    @21
    @9
    wceq
    @18
    @0
    @26
    wa
    #
    @9
    @8
    @4
    cin
    @21
    @8
    @4
    incom
    @28
    @8
    @20
    @4
    cA
    @1
    chjcom
    ineq1d
    syl5reqr
    adantlr
    @27
    @7
    @22
    @1
    chj
    co
    #
    @23
    @22
    @6
    @1
    chj
    cA
    @4
    incom
    oveq1i
    @19
    @22
    cch
    wcel
    @26
    @29
    @23
    wceq
    cA
    @4
    chincl
    @22
    @1
    chjcom
    sylan
    syl5reqr
    eqeq12d
    @9
    @7
    eqcom
    syl6bb
    imbi2d
    ralbidva
    bitrd
    ralbidva
    syl5bb
    @11
    vy
    vx
    cch
    cch
    ralcom
    syl6bb
    @0
    @14
    @12
    vx
    cch
    vy
    cA
    @1
    dmdbr
    ralbidva
    bitr4d
end
