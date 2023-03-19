include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "weu.mm"
include "wreu.mm"
include "wfn.mm"
include "ffn.mm"
include "fneu2.mm"
include "sylan.mm"
include "wb.mm"
include "opelf.mm"
include "simprd.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "eubidv.mm"
include "adantr.mm"
include "mpbid.mm"
include "df-reu.mm"
include "sylibr.mm"

theorem feu
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint F y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ( F : A --> B /\ C e. A ) -> E! y e. B <. C , y >. e. F )

  proof
    cA
    cB
    cF
    wf
    #
    cC
    cA
    wcel
    #
    wa
    #
    vy
    cv
    #
    cB
    wcel
    #
    cC
    @3
    cop
    cF
    wcel
    #
    wa
    #
    vy
    weu
    #
    @5
    vy
    cB
    wreu
    @2
    @5
    vy
    weu
    #
    @7
    @0
    cF
    cA
    wfn
    @1
    @8
    cA
    cB
    cF
    ffn
    vy
    cA
    cC
    cF
    fneu2
    sylan
    @0
    @8
    @7
    wb
    @1
    @0
    @5
    @6
    vy
    @0
    @5
    @4
    @0
    @5
    @4
    @0
    @5
    wa
    @1
    @4
    cA
    cB
    cC
    @3
    cF
    opelf
    simprd
    ex
    pm4.71rd
    eubidv
    adantr
    mpbid
    @5
    vy
    cB
    df-reu
    sylibr
end
