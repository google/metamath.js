include "wcel.mm"
include "wbr.mm"
include "w3a.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "wb.mm"
include "brcnvg.mm"
include "ancoms.mm"
include "biimp3ar.mm"
include "breldmg.mm"
include "3com12.mm"
include "syld3an3.mm"
include "df-rn.mm"
include "syl6eleqr.mm"

theorem brelrng
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( A e. F /\ B e. G /\ A C B ) -> B e. ran C )

  proof
    cA
    cF
    wcel
    #
    cB
    cG
    wcel
    #
    cA
    cB
    cC
    wbr
    #
    w3a
    cB
    cC
    ccnv
    #
    cdm
    #
    cC
    crn
    @0
    @1
    @2
    cB
    cA
    @3
    wbr
    #
    cB
    @4
    wcel
    #
    @0
    @1
    @5
    @2
    @1
    @0
    @5
    @2
    wb
    cB
    cA
    cG
    cF
    cC
    brcnvg
    ancoms
    biimp3ar
    @1
    @0
    @5
    @6
    cB
    cA
    cG
    cF
    @3
    breldmg
    3com12
    syld3an3
    cC
    df-rn
    syl6eleqr
end
