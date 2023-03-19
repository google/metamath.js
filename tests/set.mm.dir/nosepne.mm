include "csur.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "wo.mm"
include "wor.mm"
include "wb.mm"
include "sltso.mm"
include "sotrine.mm"
include "mpan.mm"
include "nosepnelem.mm"
include "3expia.mm"
include "wi.mm"
include "w3a.mm"
include "necom.mm"
include "rabbii.mm"
include "inteqi.mm"
include "fveq2i.mm"
include "neeq12i.mm"
include "bitri.mm"
include "sylibr.mm"
include "ancoms.mm"
include "jaod.mm"
include "sylbid.mm"
include "3impia.mm"

theorem nosepne
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ A =/= B ) -> ( A ` |^| { x e. On | ( A ` x ) =/= ( B ` x ) } ) =/= ( B ` |^| { x e. On | ( A ` x ) =/= ( B ` x ) } ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cA
    cB
    wne
    #
    vx
    cv
    #
    cA
    cfv
    #
    @3
    cB
    cfv
    #
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    cA
    cfv
    #
    @8
    cB
    cfv
    #
    wne
    #
    @0
    @1
    wa
    #
    @2
    cA
    cB
    cslt
    wbr
    #
    cB
    cA
    cslt
    wbr
    #
    wo
    #
    @11
    csur
    cslt
    wor
    @12
    @2
    @15
    wb
    sltso
    csur
    cA
    cB
    cslt
    sotrine
    mpan
    @12
    @13
    @11
    @14
    @0
    @1
    @13
    @11
    vx
    cA
    cB
    nosepnelem
    3expia
    @1
    @0
    @14
    @11
    wi
    @1
    @0
    @14
    @11
    @1
    @0
    @14
    w3a
    @5
    @4
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    cB
    cfv
    #
    @18
    cA
    cfv
    #
    wne
    #
    @11
    vx
    cB
    cA
    nosepnelem
    @11
    @20
    @19
    wne
    @21
    @9
    @20
    @10
    @19
    @8
    @18
    cA
    @7
    @17
    @6
    @16
    vx
    con0
    @4
    @5
    necom
    rabbii
    inteqi
    #
    fveq2i
    @8
    @18
    cB
    @22
    fveq2i
    neeq12i
    @20
    @19
    necom
    bitri
    sylibr
    3expia
    ancoms
    jaod
    sylbid
    3impia
end
