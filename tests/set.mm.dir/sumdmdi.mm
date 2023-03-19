include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "cdmd.mm"
include "wbr.mm"
include "sumdmdii.mm"
include "cv.mm"
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
include "sumdmdlem2.mm"
include "syl.mm"
include "impbii.mm"

theorem sumdmdi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH


  assert |- ( ( A +H B ) = ( A vH B ) <-> A MH* B )

  proof
    cA
    cB
    cph
    co
    cA
    cB
    chj
    co
    #
    wceq
    #
    cA
    cB
    cdmd
    wbr
    #
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    sumdmdii
    @2
    vx
    cv
    #
    cB
    chj
    co
    #
    @0
    cin
    @4
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
    @1
    @2
    @5
    vx
    cch
    wral
    #
    @6
    cA
    cch
    wcel
    cB
    cch
    wcel
    @2
    @7
    wb
    sumdmdi.1
    sumdmdi.2
    vx
    cA
    cB
    dmdbr4
    mp2an
    @5
    @5
    vx
    cch
    cat
    @3
    cat
    wcel
    @3
    cch
    wcel
    @5
    @3
    atelch
    imim1i
    ralimi2
    sylbi
    vx
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    sumdmdlem2
    syl
    impbii
end
