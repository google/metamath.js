include "cdmd.mm"
include "wbr.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "cat.mm"
include "wral.mm"
include "cch.mm"
include "wcel.mm"
include "wb.mm"
include "dmdbr4.mm"
include "mp2an.mm"
include "atelch.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "sylbi.mm"
include "cph.mm"
include "wceq.mm"
include "sumdmdlem2.mm"
include "sumdmdi.mm"
include "sylib.mm"
include "impbii.mm"

theorem dmdbr4ati
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C y
  disjoint C z
  disjoint C w
  assert |- ( A MH* B <-> A. x e. HAtoms ( ( x vH B ) i^i ( A vH B ) ) C_ ( ( ( x vH B ) i^i A ) vH B ) )

  proof
    cA
    cB
    cdmd
    wbr
    #
    vx
    cv
    #
    cB
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    cin
    @2
    cA
    cin
    cB
    chj
    co
    wss
    #
    vx
    cat
    wral
    #
    @0
    @4
    vx
    cch
    wral
    #
    @5
    cA
    cch
    wcel
    cB
    cch
    wcel
    @0
    @6
    wb
    sumdmdi.1
    sumdmdi.2
    vx
    cA
    cB
    dmdbr4
    mp2an
    @4
    @4
    vx
    cch
    cat
    @1
    cat
    wcel
    @1
    cch
    wcel
    @4
    @1
    atelch
    imim1i
    ralimi2
    sylbi
    @5
    cA
    cB
    cph
    co
    @3
    wceq
    @0
    vx
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    sumdmdlem2
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    sumdmdi
    sylib
    impbii
end
