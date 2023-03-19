include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "cdmd.mm"
include "wbr.mm"
include "cmd.mm"
include "c0h.mm"
include "wceq.mm"
include "inindir.mm"
include "chincli.mm"
include "chocini.mm"
include "eqtr3i.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wcel.mm"
include "choccli.mm"
include "breq1.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "ineq2.mm"
include "rspc2v.mm"
include "mp2an.mm"
include "ax-mp.mm"
include "mpan2.mm"
include "dmdcompli.mm"
include "mdcompli.mm"
include "3imtr4i.mm"

theorem mddmdin0i
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume mddmdin0.1: |- A e. CH
  assume mddmdin0.2: |- B e. CH
  assume mddmdin0.3: |- A. x e. CH A. y e. CH ( ( x MH* y /\ ( x i^i y ) = 0H ) -> x MH y )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( A MH* B -> A MH B )

  proof
    cA
    cA
    cB
    cin
    #
    cort
    cfv
    #
    cin
    #
    cB
    @1
    cin
    #
    cdmd
    wbr
    #
    @2
    @3
    cmd
    wbr
    #
    cA
    cB
    cdmd
    wbr
    cA
    cB
    cmd
    wbr
    @4
    @2
    @3
    cin
    #
    c0h
    wceq
    #
    @5
    @0
    @1
    cin
    @6
    c0h
    cA
    cB
    @1
    inindir
    @0
    cA
    cB
    mddmdin0.1
    mddmdin0.2
    chincli
    #
    chocini
    eqtr3i
    vx
    cv
    #
    vy
    cv
    #
    cdmd
    wbr
    #
    @9
    @10
    cin
    #
    c0h
    wceq
    #
    wa
    #
    @9
    @10
    cmd
    wbr
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    #
    @4
    @7
    wa
    #
    @5
    wi
    #
    mddmdin0.3
    @2
    cch
    wcel
    @3
    cch
    wcel
    @17
    @19
    wi
    cA
    @1
    mddmdin0.1
    @0
    @8
    choccli
    #
    chincli
    cB
    @1
    mddmdin0.2
    @20
    chincli
    @16
    @19
    @2
    @10
    cdmd
    wbr
    #
    @2
    @10
    cin
    #
    c0h
    wceq
    #
    wa
    #
    @2
    @10
    cmd
    wbr
    #
    wi
    vx
    vy
    @2
    @3
    cch
    cch
    @9
    @2
    wceq
    #
    @14
    @24
    @15
    @25
    @26
    @11
    @21
    @13
    @23
    @9
    @2
    @10
    cdmd
    breq1
    @26
    @12
    @22
    c0h
    @9
    @2
    @10
    ineq1
    eqeq1d
    anbi12d
    @9
    @2
    @10
    cmd
    breq1
    imbi12d
    @10
    @3
    wceq
    #
    @24
    @18
    @25
    @5
    @27
    @21
    @4
    @23
    @7
    @10
    @3
    @2
    cdmd
    breq2
    @27
    @22
    @6
    c0h
    @10
    @3
    @2
    ineq2
    eqeq1d
    anbi12d
    @10
    @3
    @2
    cmd
    breq2
    imbi12d
    rspc2v
    mp2an
    ax-mp
    mpan2
    cA
    cB
    mddmdin0.1
    mddmdin0.2
    dmdcompli
    cA
    cB
    mddmdin0.1
    mddmdin0.2
    mdcompli
    3imtr4i
end
