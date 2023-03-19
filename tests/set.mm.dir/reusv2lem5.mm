include "wcel.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wtru.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "weu.mm"
include "wrex.mm"
include "wreu.mm"
include "wb.mm"
include "tru.mm"
include "biimt.mm"
include "mpan2.mm"
include "ibar.mm"
include "bitr3d.mm"
include "eleq1.mm"
include "pm5.32ri.mm"
include "syl6bbr.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "eubidv.mm"
include "r19.28zv.mm"
include "sylan9bb.mm"
include "biantrur.mm"
include "rexbii.mm"
include "reubii.mm"
include "reusv2lem4.mm"
include "bitri.mm"
include "df-reu.mm"
include "3bitr4g.mm"

theorem reusv2lem5
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  assert |- ( ( A. y e. B C e. A /\ B =/= (/) ) -> ( E! x e. A E. y e. B x = C <-> E! x e. A A. y e. B x = C ) )

  proof
    cC
    cA
    wcel
    #
    vy
    cB
    wral
    #
    cB
    c0
    wne
    #
    wa
    @0
    wtru
    wa
    #
    vx
    cv
    #
    cC
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    weu
    #
    @4
    cA
    wcel
    #
    @5
    vy
    cB
    wral
    #
    wa
    #
    vx
    weu
    #
    @5
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    @10
    vx
    cA
    wreu
    @1
    @8
    @9
    @5
    wa
    #
    vy
    cB
    wral
    #
    vx
    weu
    @2
    @12
    @1
    @7
    @16
    vx
    @1
    @6
    @15
    wb
    #
    vy
    cB
    wral
    @7
    @16
    wb
    @0
    @17
    vy
    cB
    @0
    @6
    @0
    @5
    wa
    #
    @15
    @0
    @5
    @6
    @18
    @0
    wtru
    @5
    @6
    wb
    tru
    @3
    @5
    biimt
    mpan2
    @0
    @5
    ibar
    bitr3d
    @5
    @9
    @0
    @4
    cC
    cA
    eleq1
    pm5.32ri
    syl6bbr
    ralimi
    @6
    @15
    vy
    cB
    ralbi
    syl
    eubidv
    @2
    @16
    @11
    vx
    @9
    @5
    vy
    cB
    r19.28zv
    eubidv
    sylan9bb
    @14
    wtru
    @5
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    @8
    @13
    @20
    vx
    cA
    @5
    @19
    vy
    cB
    wtru
    @5
    tru
    biantrur
    rexbii
    reubii
    wtru
    vx
    vy
    cA
    cB
    cC
    reusv2lem4
    bitri
    @10
    vx
    cA
    df-reu
    3bitr4g
end
